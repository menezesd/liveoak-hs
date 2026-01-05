{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Rebuild SSA form after transformations that may violate SSA constraints.
module LiveOak.SSARebuild
  ( stripSSA
  , rebuildSSA
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (blockMapFromList, mapExpr)
import LiveOak.CFG
import LiveOak.Dominance
import LiveOak.MapUtils (lookupInt, lookupSet)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Stripping SSA (drop versions + phi nodes)
--------------------------------------------------------------------------------

-- | Strip SSA versions and phi nodes to get a non-SSA program.
stripSSA :: SSAMethod -> SSAMethod
stripSSA method@SSAMethod{..} =
  method
    { ssaMethodParams = map stripVar ssaMethodParams
    , ssaMethodBlocks = map stripBlock ssaMethodBlocks
    }

stripBlock :: SSABlock -> SSABlock
stripBlock SSABlock{..} =
  SSABlock
    { blockLabel = blockLabel
    , blockPhis = []
    , blockInstrs = map stripInstr blockInstrs
    }

stripInstr :: SSAInstr -> SSAInstr
stripInstr = \case
  SSAAssign var expr -> SSAAssign (stripVar var) (stripExpr expr)
  SSAFieldStore target field off value ->
    SSAFieldStore (stripExpr target) field off (stripExpr value)
  SSAReturn exprOpt -> SSAReturn (fmap stripExpr exprOpt)
  SSABranch cond t f -> SSABranch (stripExpr cond) t f
  SSAExprStmt expr -> SSAExprStmt (stripExpr expr)
  instr -> instr

stripExpr :: SSAExpr -> SSAExpr
stripExpr = mapExpr $ \case
  SSAUse var -> SSAUse (stripVar var)
  expr -> expr

stripVar :: SSAVar -> SSAVar
stripVar var = var { ssaVersion = 0 }

--------------------------------------------------------------------------------
-- SSA Rebuild
--------------------------------------------------------------------------------

-- | Rebuild SSA by inserting phi nodes and renaming variables.
rebuildSSA :: SSAMethod -> SSAMethod
rebuildSSA method =
  let stripped = stripSSA method
      cfg = buildCFG stripped
      domTree = computeDominators cfg
      domFrontier = computeDomFrontier cfg domTree
      defSites = findDefSites stripped
      blocksWithPhis = insertPhis cfg domFrontier defSites (ssaMethodBlocks stripped)
      renamedBlocks = renameVariablesFromParams cfg domTree (ssaMethodParams stripped) blocksWithPhis
  in stripped { ssaMethodBlocks = renamedBlocks }

--------------------------------------------------------------------------------
-- Phi Placement
--------------------------------------------------------------------------------

-- | Find all definition sites for each variable
-- Returns: variable name -> set of blocks where it's defined
findDefSites :: SSAMethod -> Map String (Set BlockId)
findDefSites method = foldl' addBlockDefs Map.empty (ssaMethodBlocks method)
  where
    addBlockDefs acc block =
      foldl' (addDef (blockLabel block)) acc (blockInstrs block)

    addDef bid acc instr = case instr of
      SSAAssign var _ ->
        Map.insertWith Set.union (varNameString (ssaName var)) (Set.singleton bid) acc
      _ -> acc

-- | Insert phi nodes at dominance frontiers of definition sites
insertPhis :: CFG -> DomFrontier -> Map String (Set BlockId) -> [SSABlock] -> [SSABlock]
insertPhis cfg domFrontier defSites blocks =
  let phiSites = Map.mapWithKey (computePhiSites domFrontier) defSites
      blockMap = blockMapFromList blocks
      blockMap' = Map.foldlWithKey' (insertPhisForVar cfg) blockMap phiSites
  in Map.elems blockMap'

-- | Compute where phi nodes are needed for a variable using dominance frontiers
computePhiSites :: DomFrontier -> String -> Set BlockId -> Set BlockId
computePhiSites domFrontier _varName defBlocks = go defBlocks Set.empty
  where
    go worklist phiBlocks
      | Set.null worklist = phiBlocks
      | otherwise =
          let (block, rest) = Set.deleteFindMin worklist
              frontier = lookupSet block domFrontier
              newPhiBlocks = Set.difference frontier phiBlocks
              newWorklist = Set.union rest (Set.difference newPhiBlocks defBlocks)
          in go newWorklist (Set.union phiBlocks newPhiBlocks)

-- | Insert phi nodes for a variable into the appropriate blocks
insertPhisForVar :: CFG -> Map BlockId SSABlock -> String -> Set BlockId -> Map BlockId SSABlock
insertPhisForVar cfg blockMap vName =
  Set.foldl' insertPhi blockMap
  where
    insertPhi bm bid =
      case Map.lookup bid bm of
        Nothing -> bm
        Just block ->
          let preds = predecessors cfg bid
              phiArgs = [(p, SSAVar (varName vName) 0 Nothing) | p <- preds]
              phi = PhiNode (SSAVar (varName vName) 0 Nothing) phiArgs
              existingPhis = blockPhis block
              hasPhiForVar = any (\p -> varNameString (ssaName (phiVar p)) == vName) existingPhis
          in if hasPhiForVar
             then bm
             else Map.insert bid (block { blockPhis = phi : existingPhis }) bm

--------------------------------------------------------------------------------
-- SSA Variable Renaming
--------------------------------------------------------------------------------

-- | Rename variables with proper SSA versioning.
renameVariablesFromParams :: CFG -> DomTree -> [SSAVar] -> [SSABlock] -> [SSABlock]
renameVariablesFromParams cfg domTree params blocks =
  let initVersions = Map.fromList [(ssaName p, 1) | p <- params]
      initDefs = Map.fromList [(ssaName p, p { ssaVersion = 0 }) | p <- params]
      initState = RenameState initVersions initDefs
      blockMap = blockMapFromList blocks
      entry = cfgEntry cfg
      (renSt, renamedMap) = if Map.member entry blockMap
        then renameBlock cfg domTree entry initState blockMap
        else (initState, blockMap)
      reachable = Set.fromList (domRPO domTree)
      unreached = Set.toList $ Set.difference (Map.keysSet blockMap) reachable
      seedUnreachable st = st { renameCurrentDef = initDefs }
      (_, finalMap) = foldl' (\(st, bm) bid ->
                                renameBlock cfg domTree bid (seedUnreachable st) bm)
                              (renSt, renamedMap)
                              unreached
  in Map.elems finalMap

data RenameState = RenameState
  { renameVersions :: !(Map VarName Int)
  , renameCurrentDef :: !(Map VarName SSAVar)
  }

renameBlock :: CFG -> DomTree -> BlockId -> RenameState -> Map BlockId SSABlock
           -> (RenameState, Map BlockId SSABlock)
renameBlock cfg domTree bid renSt blockMap =
  case Map.lookup bid blockMap of
    Nothing -> (renSt, blockMap)
    Just block ->
      let (renSt1, renamedPhis) = renamePhiDefs renSt (blockPhis block)
          (renSt2, renamedInstrs) = renameInstrs renSt1 (blockInstrs block)
          renamedBlock = block { blockPhis = renamedPhis, blockInstrs = renamedInstrs }
          blockMap1 = Map.insert bid renamedBlock blockMap
          blockMap2 = foldl' (fillPhiArgs bid renSt2) blockMap1 (successors cfg bid)
          (renSt3, blockMap3) = foldl' (processChild cfg domTree renSt2)
                                        (renSt2, blockMap2)
                                        (domChildren domTree bid)
      in (renSt3, blockMap3)

processChild :: CFG -> DomTree -> RenameState -> (RenameState, Map BlockId SSABlock) -> BlockId
            -> (RenameState, Map BlockId SSABlock)
processChild cfg domTree parentState (renSt, blockMap) childId =
  let childState = parentState { renameVersions = renameVersions renSt }
      (childState', blockMap') = renameBlock cfg domTree childId childState blockMap
      renSt' = parentState { renameVersions = renameVersions childState' }
  in (renSt', blockMap')

renamePhiDefs :: RenameState -> [PhiNode] -> (RenameState, [PhiNode])
renamePhiDefs renSt phis =
  let (st', acc) = foldl' renamePhi (renSt, []) phis
  in (st', reverse acc)
  where
    renamePhi (st, acc) phi =
      let vName = ssaName (phiVar phi)
          version = lookupInt vName (renameVersions st)
          newVar = SSAVar vName version (ssaVarType (phiVar phi))
          st' = st { renameVersions = Map.insert vName (version + 1) (renameVersions st)
                   , renameCurrentDef = Map.insert vName newVar (renameCurrentDef st)
                   }
          phi' = phi { phiVar = newVar }
      in (st', phi' : acc)

renameInstrs :: RenameState -> [SSAInstr] -> (RenameState, [SSAInstr])
renameInstrs renSt instrs =
  let (st', acc) = foldl' renameInstr (renSt, []) instrs
  in (st', reverse acc)
  where
    renameInstr (st, acc) instr = case instr of
      SSAAssign var expr ->
        let expr' = renameExpr st expr
            vName = ssaName var
            version = lookupInt vName (renameVersions st)
            newVar = SSAVar vName version (ssaVarType var)
            st' = st { renameVersions = Map.insert vName (version + 1) (renameVersions st)
                     , renameCurrentDef = Map.insert vName newVar (renameCurrentDef st)
                     }
        in (st', SSAAssign newVar expr' : acc)

      SSAFieldStore target field off value ->
        let target' = renameExpr st target
            value' = renameExpr st value
        in (st, SSAFieldStore target' field off value' : acc)

      SSAReturn exprOpt ->
        let exprOpt' = fmap (renameExpr st) exprOpt
        in (st, SSAReturn exprOpt' : acc)

      SSAJump target ->
        (st, SSAJump target : acc)

      SSABranch cond t f ->
        let cond' = renameExpr st cond
        in (st, SSABranch cond' t f : acc)

      SSAExprStmt expr ->
        let expr' = renameExpr st expr
        in (st, SSAExprStmt expr' : acc)

renameExpr :: RenameState -> SSAExpr -> SSAExpr
renameExpr renSt = \case
  SSAUse var ->
    case Map.lookup (ssaName var) (renameCurrentDef renSt) of
      Just v -> SSAUse v
      Nothing -> SSAUse var
  SSAUnary op e -> SSAUnary op (renameExpr renSt e)
  SSABinary op l r -> SSABinary op (renameExpr renSt l) (renameExpr renSt r)
  SSATernary c t e -> SSATernary (renameExpr renSt c) (renameExpr renSt t) (renameExpr renSt e)
  SSACall name args -> SSACall name (map (renameExpr renSt) args)
  SSAInstanceCall t m args -> SSAInstanceCall (renameExpr renSt t) m (map (renameExpr renSt) args)
  SSANewObject cn args -> SSANewObject cn (map (renameExpr renSt) args)
  SSAFieldAccess t f -> SSAFieldAccess (renameExpr renSt t) f
  e -> e

fillPhiArgs :: BlockId -> RenameState -> Map BlockId SSABlock -> BlockId -> Map BlockId SSABlock
fillPhiArgs predId renSt blockMap succId =
  case Map.lookup succId blockMap of
    Nothing -> blockMap
    Just block ->
      let phis' = map (fillPhiArg predId renSt) (blockPhis block)
      in Map.insert succId (block { blockPhis = phis' }) blockMap

fillPhiArg :: BlockId -> RenameState -> PhiNode -> PhiNode
fillPhiArg predId renSt phi =
  let vName = ssaName (phiVar phi)
      currentDef = Map.findWithDefault (SSAVar vName 0 Nothing) vName (renameCurrentDef renSt)
      args' = map updateArg (phiArgs phi)
      updateArg (p, v)
        | p == predId = (p, currentDef)
        | otherwise = (p, v)
  in phi { phiArgs = args' }
