{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Dead Code Elimination using SSA def-use chains.
-- More precise than traditional DCE because SSA form makes uses explicit.
module LiveOak.DCE
  ( -- * Dead Code Elimination
    eliminateDeadCode
  , DCEResult(..)

    -- * Def-Use Chains
  , DefUseChains
  , buildDefUseChains
  , getUses
  , getDef
  ) where

import LiveOak.SSATypes
import LiveOak.MapUtils (lookupSet)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Def-Use Chains
--------------------------------------------------------------------------------

-- | Definition site: block + instruction index
data DefSite = DefSite
  { defBlock :: !BlockId
  , defIndex :: !Int        -- ^ -1 for phi, >= 0 for instruction
  } deriving (Eq, Ord, Show)

-- | Use site: block + instruction index + operand position
data UseSite = UseSite
  { useBlock :: !BlockId
  , useIndex :: !Int
  } deriving (Eq, Ord, Show)

-- | Def-use chains
data DefUseChains = DefUseChains
  { ducDefs :: !(Map String DefSite)       -- ^ Variable -> definition site
  , ducUses :: !(Map String (Set UseSite)) -- ^ Variable -> use sites
  } deriving (Show)

-- | Build def-use chains from SSA blocks
buildDefUseChains :: [SSABlock] -> DefUseChains
buildDefUseChains blocks =
  let -- Collect definitions
      defs = foldl' collectDefs Map.empty blocks
      -- Collect uses
      uses = foldl' collectUses Map.empty blocks
  in DefUseChains { ducDefs = defs, ducUses = uses }

-- | Collect definitions from a block
collectDefs :: Map String DefSite -> SSABlock -> Map String DefSite
collectDefs acc SSABlock{..} =
  let -- Phi definitions
      phiDefs = [(varNameString (ssaName (phiVar phi)), DefSite blockLabel (-1)) | phi <- blockPhis]
      -- Instruction definitions
      instrDefs = [(varNameString (ssaName var), DefSite blockLabel i)
                  | (i, SSAAssign var _) <- zip [0..] blockInstrs]
  in foldl' (\m (k, v) -> Map.insert k v m) acc (phiDefs ++ instrDefs)

-- | Collect uses from a block
collectUses :: Map String (Set UseSite) -> SSABlock -> Map String (Set UseSite)
collectUses acc SSABlock{..} =
  let -- Phi uses
      phiUses = [(varNameString (ssaName argVar), UseSite blockLabel (-1))
                | phi <- blockPhis
                , (_, argVar) <- phiArgs phi]
      -- Instruction uses
      instrUses = [(var, UseSite blockLabel i)
                  | (i, instr) <- zip [0..] blockInstrs
                  , var <- instrVarUses instr]
      allUses = phiUses ++ instrUses
  in foldl' addUse acc allUses
  where
    addUse m (var, site) = Map.insertWith Set.union var (Set.singleton site) m

-- | Get variable uses from an instruction
instrVarUses :: SSAInstr -> [String]
instrVarUses = \case
  SSAAssign _ expr -> exprVarUses expr
  SSAReturn (Just expr) -> exprVarUses expr
  SSAReturn Nothing -> []
  SSAJump _ -> []
  SSABranch cond _ _ -> exprVarUses cond
  SSAFieldStore target _ _ value -> exprVarUses target ++ exprVarUses value
  SSAExprStmt expr -> exprVarUses expr

-- | Get variable uses from an expression
exprVarUses :: SSAExpr -> [String]
exprVarUses = \case
  SSAInt _ -> []
  SSABool _ -> []
  SSAStr _ -> []
  SSANull -> []
  SSAThis -> []
  SSAUse var -> [varNameString (ssaName var)]
  SSAUnary _ e -> exprVarUses e
  SSABinary _ l r -> exprVarUses l ++ exprVarUses r
  SSATernary c t e -> exprVarUses c ++ exprVarUses t ++ exprVarUses e
  SSACall _ args -> concatMap exprVarUses args
  SSAInstanceCall target _ args -> exprVarUses target ++ concatMap exprVarUses args
  SSANewObject _ args -> concatMap exprVarUses args
  SSAFieldAccess target _ -> exprVarUses target

-- | Get uses of a variable
getUses :: DefUseChains -> String -> Set UseSite
getUses duc var = lookupSet var (ducUses duc)

-- | Get definition site of a variable
getDef :: DefUseChains -> String -> Maybe DefSite
getDef duc var = Map.lookup var (ducDefs duc)

--------------------------------------------------------------------------------
-- Dead Code Elimination
--------------------------------------------------------------------------------

-- | DCE result
data DCEResult = DCEResult
  { dceOptBlocks :: ![SSABlock]   -- ^ Optimized blocks
  , dceEliminated :: !Int         -- ^ Number of eliminated instructions
  } deriving (Show)

-- | Eliminate dead code using def-use chains
eliminateDeadCode :: [SSABlock] -> DCEResult
eliminateDeadCode blocks =
  let -- Find essential variables (used in returns, branches, stores, calls)
      essential = findEssentialVars blocks
      -- Mark all live variables (reachable from essential)
      -- This properly follows phi arguments when a phi is live
      live = markLiveWithBlocks blocks essential
      -- Remove dead definitions
      (optimized, count) = removeDeadDefs live blocks
  in DCEResult
    { dceOptBlocks = optimized
    , dceEliminated = count
    }

-- | Find essential variables (those that must be kept)
findEssentialVars :: [SSABlock] -> Set String
findEssentialVars blocks = Set.fromList $ concatMap blockEssential blocks
  where
    blockEssential SSABlock{..} = concatMap instrEssential blockInstrs

    instrEssential = \case
      SSAReturn (Just expr) -> exprVarUses expr
      SSABranch cond _ _ -> exprVarUses cond
      SSAFieldStore target _ _ value -> exprVarUses target ++ exprVarUses value
      SSAExprStmt expr -> exprVarUses expr  -- Side effects
      SSAAssign _ (SSACall _ args) -> concatMap exprVarUses args  -- Calls have side effects
      SSAAssign _ (SSAInstanceCall target _ args) ->
        exprVarUses target ++ concatMap exprVarUses args
      SSAAssign _ (SSANewObject _ args) -> concatMap exprVarUses args  -- Allocation
      _ -> []

-- | Mark all live variables by following def-use chains
-- When a variable is live, all variables used in its definition are also live.
-- For phi nodes, this means all argument variables become live.
markLive :: DefUseChains -> Set String -> Set String
markLive _duc initial = go initial (Set.toList initial)
  where
    go live [] = live
    go live (var:worklist) =
      -- Already processed - skip
      if Set.member var live && var `notElem` worklist
        then go live worklist
        else go live worklist  -- We add all initial as live, just process worklist

-- | Extended version that works with blocks to properly trace phi arguments
markLiveWithBlocks :: [SSABlock] -> Set String -> Set String
markLiveWithBlocks blocks initial = go initial (Set.toList initial)
  where
    -- Build maps for quick lookup
    defMap = buildDefMap blocks       -- var -> (block, defining instruction/phi)

    go live [] = live
    go live (var:worklist) =
      case Map.lookup var defMap of
        Nothing -> go live worklist  -- External (parameter)
        Just (DefInPhi phi) ->
          -- Phi is live: all its arguments must be live too
          let argVars = [varNameString (ssaName v) | (_, v) <- phiArgs phi]
              newVars = filter (`Set.notMember` live) argVars
              live' = Set.union live (Set.fromList newVars)
          in go live' (worklist ++ newVars)
        Just (DefInInstr instr) ->
          -- Instruction is live: all variables it uses must be live too
          let usedVars = instrVarUses instr
              newVars = filter (`Set.notMember` live) usedVars
              live' = Set.union live (Set.fromList newVars)
          in go live' (worklist ++ newVars)

-- | Definition location
data DefLoc = DefInPhi !PhiNode | DefInInstr !SSAInstr
  deriving (Show)

-- | Build a map from variable name to its defining instruction/phi
buildDefMap :: [SSABlock] -> Map String DefLoc
buildDefMap blocks = Map.fromList $ concatMap blockDefs blocks
  where
    blockDefs SSABlock{..} =
      let phiDefs = [(varNameString (ssaName (phiVar phi)), DefInPhi phi) | phi <- blockPhis]
          instrDefs = [(varNameString (ssaName var), DefInInstr instr)
                      | instr@(SSAAssign var _) <- blockInstrs]
      in phiDefs ++ instrDefs

-- | Remove dead definitions
removeDeadDefs :: Set String -> [SSABlock] -> ([SSABlock], Int)
removeDeadDefs live blocks =
  let results = map (removeBlockDeadDefs live) blocks
      optimized = map fst results
      count = sum (map snd results)
  in (optimized, count)

-- | Remove dead definitions from a block
removeBlockDeadDefs :: Set String -> SSABlock -> (SSABlock, Int)
removeBlockDeadDefs live block@SSABlock{..} =
  let -- Filter phi nodes
      (livePhis, deadPhiCount) = filterPhis live blockPhis
      -- Filter instructions
      (liveInstrs, deadInstrCount) = filterInstrs live blockInstrs
  in ( block { blockPhis = livePhis, blockInstrs = liveInstrs }
     , deadPhiCount + deadInstrCount
     )

-- | Filter phi nodes, keeping only live ones
filterPhis :: Set String -> [PhiNode] -> ([PhiNode], Int)
filterPhis live phis =
  let livePhis = filter (isLivePhi live) phis
      totalCount = length phis
      liveCount = length livePhis
  in (livePhis, totalCount - liveCount)
  where
    isLivePhi liveSet phi = Set.member (varNameString (ssaName (phiVar phi))) liveSet

-- | Filter instructions, keeping only live ones or those with side effects
filterInstrs :: Set String -> [SSAInstr] -> ([SSAInstr], Int)
filterInstrs live instrs =
  let liveInstrs = filter (isLiveInstr live) instrs
      totalCount = length instrs
      liveCount = length liveInstrs
  in (liveInstrs, totalCount - liveCount)
  where
    isLiveInstr liveSet = \case
      SSAAssign var expr ->
        Set.member (varNameString (ssaName var)) liveSet || hasSideEffects expr
      -- Always keep terminators and side-effecting instructions
      SSAReturn _ -> True
      SSAJump _ -> True
      SSABranch _ _ _ -> True
      SSAFieldStore _ _ _ _ -> True
      SSAExprStmt _ -> True

    hasSideEffects = \case
      SSACall _ _ -> True
      SSAInstanceCall _ _ _ -> True
      SSANewObject _ _ -> True  -- Allocation
      SSAUnary _ e -> hasSideEffects e
      SSABinary _ l r -> hasSideEffects l || hasSideEffects r
      SSATernary c t e -> hasSideEffects c || hasSideEffects t || hasSideEffects e
      _ -> False
