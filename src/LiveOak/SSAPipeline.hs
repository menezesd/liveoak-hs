{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Unified SSA Optimization Pipeline.
-- Provides a configurable optimization pipeline that integrates:
-- - OptConfig for pass selection
-- - OptContext for cached analysis
-- - OptStats for statistics tracking
--
-- == Usage
--
-- @
-- let config = defaultOptConfig
--     (optimized, stats) = runPipeline config symbols ssaProgram
-- @
--
module LiveOak.SSAPipeline
  ( -- * Pipeline Execution
    runPipeline
  , runPipelineWithConfig
  , runMethodPipeline

    -- * Configuration (re-exported)
  , OptConfig(..)
  , PassFlags(..)
  , defaultOptConfig
  , aggressiveOptConfig
  , minimalOptConfig

    -- * Statistics (re-exported)
  , OptStats(..)
  , showStats
  ) where

import LiveOak.SSATypes
import LiveOak.Symbol (ProgramSymbols)
import LiveOak.OptConfig
import LiveOak.OptStats
import LiveOak.OptContext (OptContext(..), buildOptContext)

import qualified LiveOak.GVN as GVN
import qualified LiveOak.LICM as LICM
import qualified LiveOak.LCSSA as LCSSA
import qualified LiveOak.PRE as PRE
import qualified LiveOak.SCCP as SCCP
import qualified LiveOak.TailCall as TCO
import qualified LiveOak.StrengthReduce as SR
import qualified LiveOak.Inline as Inline
import qualified LiveOak.DSE as DSE
import qualified LiveOak.JumpThread as JT
import qualified LiveOak.SROA as SROA
import qualified LiveOak.Unroll as Unroll
import qualified LiveOak.SSAOptimize as Opt
import qualified LiveOak.Schedule as Sched
import qualified LiveOak.BlockMerge as BM
import qualified LiveOak.NullCheck as NC
import qualified LiveOak.DeadArg as DA
import qualified LiveOak.ReturnProp as RP
import qualified LiveOak.Algebraic as Alg
import qualified LiveOak.Reassoc as Rea
import qualified LiveOak.LoadElim as LE
import qualified LiveOak.InstCombine as IC
import LiveOak.CFG (buildCFG)

import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as Map

--------------------------------------------------------------------------------
-- Pipeline Execution
--------------------------------------------------------------------------------

-- | Run the full optimization pipeline with default configuration
runPipeline :: ProgramSymbols -> SSAProgram -> (SSAProgram, OptStats)
runPipeline = runPipelineWithConfig defaultOptConfig

-- | Run the full optimization pipeline with custom configuration
runPipelineWithConfig :: OptConfig -> ProgramSymbols -> SSAProgram -> (SSAProgram, OptStats)
runPipelineWithConfig config@OptConfig{..} syms prog =
  let -- Run SROA if enabled (before main pipeline)
      (prog1, sroaStats) = if pfSROA ocPasses
        then runSROA syms prog
        else (prog, emptyStats)
      -- Run DeadArg if enabled (interprocedural, before main pipeline)
      (prog2, deadArgStats) = if pfDeadArg ocPasses
        then runDeadArg prog1
        else (prog1, emptyStats)
      -- Run main pipeline iterations
      (prog3, iterStats) = runIterations config ocIterations prog2 emptyStats
      -- Run ReturnProp if enabled (interprocedural, after main pipeline)
      (prog4, returnPropStats) = if pfReturnProp ocPasses
        then runReturnProp prog3
        else (prog3, emptyStats)
  in (prog4, combineStats sroaStats $ combineStats deadArgStats $ combineStats iterStats returnPropStats)

-- | Run the pipeline on a single method
-- Note: This creates a temporary program wrapper, so SROA is disabled
runMethodPipeline :: OptConfig -> SSAMethod -> (SSAMethod, OptStats)
runMethodPipeline config method =
  let config' = config { ocPasses = (ocPasses config) { pfSROA = False } }
      tempProg = SSAProgram [SSAClass "Temp" [] [method]]
      -- Run iterations directly (skip SROA since we don't have symbols)
      (SSAProgram classes, stats) = runIterations config' (ocIterations config') tempProg emptyStats
  in case classes of
    [cls] -> case ssaClassMethods cls of
      [m] -> (m, stats)
      _ -> (method, stats)  -- Shouldn't happen
    _ -> (method, stats)  -- Shouldn't happen

--------------------------------------------------------------------------------
-- Pipeline Iterations
--------------------------------------------------------------------------------

-- | Run multiple iterations until fixed point or max iterations reached
runIterations :: OptConfig -> Int -> SSAProgram -> OptStats -> (SSAProgram, OptStats)
runIterations _ 0 prog stats = (prog, stats)
runIterations config n prog stats =
  let (prog', iterStats) = runOneIteration config prog
      stats' = combineStats stats iterStats
  in if prog' == prog
     then (prog', stats')  -- Fixed point reached
     else runIterations config (n - 1) prog' stats'

-- | Run one iteration of the pipeline
runOneIteration :: OptConfig -> SSAProgram -> (SSAProgram, OptStats)
runOneIteration OptConfig{..} prog =
  let flags = ocPasses
      -- Chain passes conditionally based on flags
      -- Phase 1: Early simplifications
      (p1, s1) = applyPassIf (pfSimplifyPhis flags) "SimplifyPhis" (noStats Opt.simplifyPhis) prog
      (p2, s2) = applyPassIf (pfAlgebraic flags) "Algebraic" runAlgebraic p1
      (p3, s3) = applyPassIf (pfReassoc flags) "Reassoc" runReassoc p2
      (p4, s4) = applyPassIf (pfInstCombine flags) "InstCombine" runInstCombine p3

      -- Phase 2: Control flow optimizations
      (p5, s5) = applyPassIf (pfTailCall flags) "TailCall" (noStats runTailCall) p4
      (p6, s6) = applyPassIf (pfInline flags) "Inline" (noStats runInline) p5
      (p7, s7) = applyPassIf (pfJumpThread flags) "JumpThread" runJumpThread p6
      (p8, s8) = applyPassIf (pfBlockMerge flags) "BlockMerge" runBlockMerge p7

      -- Phase 3: Dataflow optimizations
      (p9, s9) = applyPassIf (pfSCCP flags) "SCCP" (noStats runSCCP) p8
      (p10, s10) = applyPassIf (pfGVN flags) "GVN" (noStats runGVN) p9
      (p11, s11) = applyPassIf (pfPRE flags) "PRE" (noStats runPRE) p10
      (p12, s12) = applyPassIf (pfLoadElim flags) "LoadElim" runLoadElim p11
      (p13, s13) = applyPassIf (pfNullCheck flags) "NullCheck" runNullCheck p12

      -- Phase 4: Loop optimizations
      (p14, s14) = applyPassIf (pfLICM flags) "LICM" (noStats runLICM) p13
      (p15, s15) = applyPassIf (pfLCSSA flags) "LCSSA" runLCSSA p14
      (p16, s16) = applyPassIf (pfLoopUnroll flags) "LoopUnroll" runUnroll p15
      (p17, s17) = applyPassIf (pfStrengthReduce flags) "StrengthReduce" (noStats runStrengthReduce) p16

      -- Phase 5: Cleanup passes
      (p18, s18) = applyPassIf (pfDSE flags) "DSE" runDSE p17
      (p19, s19) = applyPassIf (pfCopyProp flags) "CopyProp" (noStats Opt.ssaCopyProp) p18
      (p20, s20) = applyPassIf (pfPeephole flags) "Peephole" (noStats Opt.ssaPeephole) p19
      (p21, s21) = applyPassIf (pfDCE flags) "DCE" (noStats Opt.ssaDeadCodeElim) p20
      (p22, s22) = applyPassIf (pfSchedule flags) "Schedule" runSchedule p21

      allStats = foldr combineStats emptyStats
        [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22]
  in (p22, allStats)

-- | Apply a pass if the flag is enabled
applyPassIf :: Bool -> String -> (SSAProgram -> (SSAProgram, PassStats)) -> SSAProgram -> (SSAProgram, OptStats)
applyPassIf False _ _ prog = (prog, emptyStats)
applyPassIf True name passFunc prog =
  let (prog', passStats) = passFunc prog
  in (prog', addPassStats name passStats emptyStats)

-- | Wrap a pass that doesn't return stats
noStats :: (SSAProgram -> SSAProgram) -> SSAProgram -> (SSAProgram, PassStats)
noStats f prog = (f prog, PassStats 1 1)

--------------------------------------------------------------------------------
-- Individual Pass Wrappers
--------------------------------------------------------------------------------

-- | Run SROA with stats
runSROA :: ProgramSymbols -> SSAProgram -> (SSAProgram, OptStats)
runSROA syms (SSAProgram classes) =
  let results = [(cls, map (SROA.scalarReplace syms) (ssaClassMethods cls)) | cls <- classes]
      totalReplaced = sum [SROA.sroaReplacedAllocs r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = SROA.sroaOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, addPassStats "SROA" (PassStats totalReplaced 1) emptyStats)

-- | Tail call optimization
runTailCall :: SSAProgram -> SSAProgram
runTailCall (SSAProgram classes) = SSAProgram (map optimizeClass classes)
  where
    optimizeClass cls = cls { ssaClassMethods = map TCO.optimizeMethodTailCalls (ssaClassMethods cls) }

-- | Inlining
runInline :: SSAProgram -> SSAProgram
runInline prog =
  let result = Inline.inlineFunctions Inline.defaultHeuristics prog
  in Inline.inlineOptProgram result

-- | Jump threading with stats
runJumpThread :: SSAProgram -> (SSAProgram, PassStats)
runJumpThread (SSAProgram classes) =
  let results = [(cls, map jtMethod (ssaClassMethods cls)) | cls <- classes]
      totalThreaded = sum [JT.jtThreaded r | (_, methods) <- results, (_, r) <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = JT.jtOptBlocks r
                                                         , ssaEntryBlock = fromMaybe (ssaEntryBlock m) (JT.jtNewEntry r) }
                                                       | (m, r) <- methods] }
                             | (cls, methods) <- results]
  in (optimized, PassStats totalThreaded 1)
  where
    jtMethod m =
      let r = JT.threadJumpsWithEntry (ssaEntryBlock m) (ssaMethodBlocks m)
      in (m, r)

-- | SCCP
runSCCP :: SSAProgram -> SSAProgram
runSCCP (SSAProgram classes) =
  SSAProgram [c { ssaClassMethods = map sccpMethod (ssaClassMethods c) } | c <- classes]

sccpMethod :: SSAMethod -> SSAMethod
sccpMethod method =
  let ctx = buildOptContext method
      paramKeys = [(ssaName p, ssaVersion p) | p <- ssaMethodParams method]
      sccpResult = SCCP.runSCCP paramKeys (octCFG ctx) (ssaMethodBlocks method)
      constMap = Map.mapMaybe SCCP.getConstant (SCCP.sccpConstValues sccpResult)
      blocks' = map (applyConstPropagation constMap) (ssaMethodBlocks method)
      liveBlocks = filter (\b -> blockLabel b `elem` SCCP.sccpReachableBlocks sccpResult) blocks'
  in method { ssaMethodBlocks = liveBlocks }

applyConstPropagation :: Map.Map VarKey SSAExpr -> SSABlock -> SSABlock
applyConstPropagation consts block =
  block { blockInstrs = map (sccpSubstInstr consts) (blockInstrs block) }

sccpSubstInstr :: Map.Map VarKey SSAExpr -> SSAInstr -> SSAInstr
sccpSubstInstr consts = \case
  SSAAssign v e -> SSAAssign v (sccpSubstExpr consts e)
  SSAFieldStore t f off val -> SSAFieldStore (sccpSubstExpr consts t) f off (sccpSubstExpr consts val)
  SSAReturn e -> SSAReturn (sccpSubstExpr consts <$> e)
  SSABranch c t f -> SSABranch (sccpSubstExpr consts c) t f
  SSAExprStmt e -> SSAExprStmt (sccpSubstExpr consts e)
  i -> i

sccpSubstExpr :: Map.Map VarKey SSAExpr -> SSAExpr -> SSAExpr
sccpSubstExpr consts = \case
  SSAUse v -> case Map.lookup (ssaName v, ssaVersion v) consts of
                Just replacement -> replacement
                Nothing -> SSAUse v
  SSAUnary op e -> SSAUnary op (sccpSubstExpr consts e)
  SSABinary op l r -> SSABinary op (sccpSubstExpr consts l) (sccpSubstExpr consts r)
  SSATernary c t e -> SSATernary (sccpSubstExpr consts c) (sccpSubstExpr consts t) (sccpSubstExpr consts e)
  SSACall n args -> SSACall n (map (sccpSubstExpr consts) args)
  SSAInstanceCall t m args -> SSAInstanceCall (sccpSubstExpr consts t) m (map (sccpSubstExpr consts) args)
  SSANewObject cn args -> SSANewObject cn (map (sccpSubstExpr consts) args)
  SSAFieldAccess t f -> SSAFieldAccess (sccpSubstExpr consts t) f
  e -> e

-- | GVN
runGVN :: SSAProgram -> SSAProgram
runGVN (SSAProgram classes) = SSAProgram (map gvnClass classes)
  where
    gvnClass c = c { ssaClassMethods = map gvnMethod (ssaClassMethods c) }
    gvnMethod method =
      let ctx = buildOptContext method
          gvnResult = GVN.runGVN (octCFG ctx) (octDomTree ctx) (ssaMethodBlocks method)
      in method { ssaMethodBlocks = GVN.gvnOptBlocks gvnResult }

-- | PRE
runPRE :: SSAProgram -> SSAProgram
runPRE (SSAProgram classes) = SSAProgram (map preClass classes)
  where
    preClass c = c { ssaClassMethods = map preMethod (ssaClassMethods c) }
    preMethod method =
      let ctx = buildOptContext method
          preResult = PRE.eliminatePartialRedundancy (octCFG ctx) (octDomTree ctx) (ssaMethodBlocks method)
      in method { ssaMethodBlocks = PRE.preOptBlocks preResult }

-- | LICM
runLICM :: SSAProgram -> SSAProgram
runLICM (SSAProgram classes) = SSAProgram (map licmClass classes)
  where
    licmClass c = c { ssaClassMethods = map licmMethod (ssaClassMethods c) }
    licmMethod method =
      let ctx = buildOptContext method
          licmResult = LICM.runLICM (octCFG ctx) (octDomTree ctx) (octLoopNest ctx) (ssaMethodBlocks method)
      in method { ssaMethodBlocks = LICM.licmOptBlocks licmResult }

-- | LCSSA with stats
runLCSSA :: SSAProgram -> (SSAProgram, PassStats)
runLCSSA (SSAProgram classes) =
  let results = [(cls, map LCSSA.transformLCSSAMethod (ssaClassMethods cls)) | cls <- classes]
      totalAdded = sum [LCSSA.lcssaPhisAdded r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = LCSSA.lcssaOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalAdded 1)

-- | Strength Reduction
runStrengthReduce :: SSAProgram -> SSAProgram
runStrengthReduce (SSAProgram classes) = SSAProgram (map srClass classes)
  where
    srClass c = c { ssaClassMethods = map srMethod (ssaClassMethods c) }
    srMethod method =
      let ctx = buildOptContext method
          srResult = SR.reduceStrength (octCFG ctx) (octDomTree ctx) (octLoopNest ctx) (ssaMethodBlocks method)
      in method { ssaMethodBlocks = SR.srOptBlocks srResult }

-- | Loop unrolling with stats
runUnroll :: SSAProgram -> (SSAProgram, PassStats)
runUnroll (SSAProgram classes) =
  let results = [(cls, map (Unroll.unrollLoops Unroll.defaultUnrollConfig) (ssaClassMethods cls)) | cls <- classes]
      totalUnrolled = sum [Unroll.urFullyUnrolled r + Unroll.urPartiallyUnrolled r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = Unroll.urOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalUnrolled 1)

-- | DSE with stats
runDSE :: SSAProgram -> (SSAProgram, PassStats)
runDSE (SSAProgram classes) =
  let results = [(cls, map (\m -> DSE.eliminateDeadStores (ssaMethodBlocks m)) (ssaClassMethods cls)) | cls <- classes]
      totalEliminated = sum [DSE.dseEliminated r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = DSE.dseOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalEliminated 1)

-- | Instruction scheduling with stats
runSchedule :: SSAProgram -> (SSAProgram, PassStats)
runSchedule (SSAProgram classes) =
  let results = [(cls, map scheduleMethod (ssaClassMethods cls)) | cls <- classes]
      totalCyclesSaved = sum [Sched.schedCyclesSaved r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = Sched.schedOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalCyclesSaved 1)
  where
    scheduleMethod method =
      let cfg = buildCFG method
      in Sched.scheduleMethod cfg (ssaMethodBlocks method)

--------------------------------------------------------------------------------
-- New Optimization Pass Wrappers
--------------------------------------------------------------------------------

-- | Algebraic simplification with stats
runAlgebraic :: SSAProgram -> (SSAProgram, PassStats)
runAlgebraic (SSAProgram classes) =
  let results = [(cls, map (\m -> Alg.simplifyAlgebraic (ssaMethodBlocks m)) (ssaClassMethods cls)) | cls <- classes]
      totalSimplified = sum [Alg.arSimplified r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = Alg.arOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalSimplified 1)

-- | Expression reassociation with stats
runReassoc :: SSAProgram -> (SSAProgram, PassStats)
runReassoc (SSAProgram classes) =
  let results = [(cls, map (\m -> Rea.reassociate (ssaMethodBlocks m)) (ssaClassMethods cls)) | cls <- classes]
      totalReassoc = sum [Rea.rrReassociated r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = Rea.rrOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalReassoc 1)

-- | Instruction combining with stats
runInstCombine :: SSAProgram -> (SSAProgram, PassStats)
runInstCombine (SSAProgram classes) =
  let results = [(cls, map (\m -> IC.combineInstrs (ssaMethodBlocks m)) (ssaClassMethods cls)) | cls <- classes]
      totalCombined = sum [IC.icCombined r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = IC.icOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalCombined 1)

-- | Block merging with stats
runBlockMerge :: SSAProgram -> (SSAProgram, PassStats)
runBlockMerge (SSAProgram classes) =
  let results = [(cls, map (\m -> BM.mergeBlocks (ssaMethodBlocks m)) (ssaClassMethods cls)) | cls <- classes]
      totalMerged = sum [BM.bmMerged r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = BM.bmOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalMerged 1)

-- | Load elimination with stats
runLoadElim :: SSAProgram -> (SSAProgram, PassStats)
runLoadElim (SSAProgram classes) =
  let results = [(cls, map (\m -> LE.eliminateLoads (ssaMethodBlocks m)) (ssaClassMethods cls)) | cls <- classes]
      totalElim = sum [LE.leEliminated r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = LE.leOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalElim 1)

-- | Null check elimination with stats
runNullCheck :: SSAProgram -> (SSAProgram, PassStats)
runNullCheck (SSAProgram classes) =
  let results = [(cls, map (\m -> NC.eliminateNullChecksMethod m) (ssaClassMethods cls)) | cls <- classes]
      totalElim = sum [NC.ncEliminated r | (_, methods) <- results, r <- methods]
      optimized = SSAProgram [cls { ssaClassMethods = [m { ssaMethodBlocks = NC.ncOptBlocks r }
                                                       | (m, r) <- zip (ssaClassMethods cls) rs] }
                             | (cls, rs) <- results]
  in (optimized, PassStats totalElim 1)

-- | Dead argument elimination with stats (whole-program pass)
runDeadArg :: SSAProgram -> (SSAProgram, OptStats)
runDeadArg prog =
  let result = DA.eliminateDeadArgs prog
  in (DA.daOptProgram result, addPassStats "DeadArg" (PassStats (DA.daEliminatedArgs result) 1) emptyStats)

-- | Return value propagation with stats (whole-program pass)
runReturnProp :: SSAProgram -> (SSAProgram, OptStats)
runReturnProp prog =
  let result = RP.propagateReturns prog
  in (RP.rpOptProgram result, addPassStats "ReturnProp" (PassStats (RP.rpPropagated result) 1) emptyStats)

