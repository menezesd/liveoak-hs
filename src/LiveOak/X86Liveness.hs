{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Liveness analysis for x86_64 register allocation.
-- Computes which SSA variables are live at each point in the program.
module LiveOak.X86Liveness
  ( -- * Types
    LivenessInfo(..)
  , LiveInterval(..)

    -- * Analysis
  , computeLiveness
  , buildIntervals
  , blockUses
  , blockDefs
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl', sortBy)
import Data.Ord (comparing)

import LiveOak.SSATypes
import LiveOak.CFG

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Liveness information for all blocks
data LivenessInfo = LivenessInfo
  { liveIn  :: !(Map BlockId (Set String))  -- ^ Variables live at block entry
  , liveOut :: !(Map BlockId (Set String))  -- ^ Variables live at block exit
  } deriving (Eq, Show)

-- | A live interval for a variable
data LiveInterval = LiveInterval
  { liVar   :: !String       -- ^ Variable name (name_version)
  , liStart :: !Int          -- ^ First definition/use position
  , liEnd   :: !Int          -- ^ Last use position
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Liveness Analysis
--------------------------------------------------------------------------------

-- | Compute liveness information using backward dataflow analysis.
-- Iterates until a fixed point is reached.
computeLiveness :: CFG -> LivenessInfo
computeLiveness cfg =
  let blocks = allBlockIds cfg
      -- Initialize with empty sets
      initInfo = LivenessInfo
        { liveIn = Map.fromList [(b, Set.empty) | b <- blocks]
        , liveOut = Map.fromList [(b, Set.empty) | b <- blocks]
        }
  in fixpoint cfg initInfo

-- | Iterate until fixed point
fixpoint :: CFG -> LivenessInfo -> LivenessInfo
fixpoint cfg info =
  let info' = iterateLiveness cfg info
  in if info' == info
     then info
     else fixpoint cfg info'

-- | Single iteration of liveness analysis
iterateLiveness :: CFG -> LivenessInfo -> LivenessInfo
iterateLiveness cfg info =
  foldl' (updateBlock cfg) info (allBlockIds cfg)

-- | Update liveness info for a single block
updateBlock :: CFG -> LivenessInfo -> BlockId -> LivenessInfo
updateBlock cfg info bid =
  case getBlock cfg bid of
    Nothing -> info
    Just block ->
      let -- live_out = union of successor live_in sets
          succBlocks = successors cfg bid
          newLiveOut = Set.unions [Map.findWithDefault Set.empty s (liveIn info)
                                  | s <- succBlocks]

          -- For phi nodes in successors, add the variables they need from this block
          phiUses = Set.fromList
            [ varStr var
            | succBid <- succBlocks
            , Just succBlock <- [getBlock cfg succBid]
            , phi <- cfgPhis succBlock
            , (predBid, var) <- phiArgs phi
            , predBid == bid
            ]

          newLiveOutWithPhis = Set.union newLiveOut phiUses

          -- live_in = uses ∪ (live_out - defs)
          uses = blockUsesCFG block
          defs = blockDefsCFG block
          newLiveIn = Set.union uses (Set.difference newLiveOutWithPhis defs)

      in info
           { liveIn = Map.insert bid newLiveIn (liveIn info)
           , liveOut = Map.insert bid newLiveOutWithPhis (liveOut info)
           }

--------------------------------------------------------------------------------
-- Use/Def Analysis
--------------------------------------------------------------------------------

-- | Get variables used in a CFG block (before being defined)
blockUsesCFG :: CFGBlock -> Set String
blockUsesCFG CFGBlock{..} =
  let -- Phi nodes define variables, don't count as uses here
      -- Uses in phi nodes are handled via liveOut of predecessors
      instrUses = Set.unions (map instrUsesSet cfgInstrs)
      termUses = terminatorUses cfgTerm
  in Set.union instrUses termUses

-- | Get variables defined in a CFG block
blockDefsCFG :: CFGBlock -> Set String
blockDefsCFG CFGBlock{..} =
  let phiDefs = Set.fromList [varStr (phiVar phi) | phi <- cfgPhis]
      instrDefs = Set.unions (map instrDefsSet cfgInstrs)
  in Set.union phiDefs instrDefs

-- | Get variables used in an SSA block (for external use)
blockUses :: SSABlock -> Set String
blockUses SSABlock{..} =
  let instrUses = Set.unions (map instrUsesSet blockInstrs)
  in instrUses

-- | Get variables defined in an SSA block (for external use)
blockDefs :: SSABlock -> Set String
blockDefs SSABlock{..} =
  let phiDefs = Set.fromList [varStr (phiVar phi) | phi <- blockPhis]
      instrDefs = Set.unions (map instrDefsSet blockInstrs)
  in Set.union phiDefs instrDefs

-- | Get variables used in an instruction
instrUsesSet :: SSAInstr -> Set String
instrUsesSet = \case
  SSAAssign _ expr -> exprUses expr
  SSAFieldStore target _ _ value ->
    Set.union (exprUses target) (exprUses value)
  SSAReturn (Just expr) -> exprUses expr
  SSAReturn Nothing -> Set.empty
  SSAJump _ -> Set.empty
  SSABranch cond _ _ -> exprUses cond
  SSAExprStmt expr -> exprUses expr

-- | Get variable defined in an instruction (if any)
instrDefsSet :: SSAInstr -> Set String
instrDefsSet = \case
  SSAAssign var _ -> Set.singleton (varStr var)
  _ -> Set.empty

-- | Get variables used in a terminator
terminatorUses :: Terminator -> Set String
terminatorUses = \case
  TermJump _ -> Set.empty
  TermBranch cond _ _ -> exprUses cond
  TermReturn (Just expr) -> exprUses expr
  TermReturn Nothing -> Set.empty

-- | Get variables used in an expression
exprUses :: SSAExpr -> Set String
exprUses = \case
  SSAInt _ -> Set.empty
  SSABool _ -> Set.empty
  SSAStr _ -> Set.empty
  SSANull -> Set.empty
  SSAUse var -> Set.singleton (varStr var)
  SSAThis -> Set.singleton "this_0"
  SSAUnary _ e -> exprUses e
  SSABinary _ l r -> Set.union (exprUses l) (exprUses r)
  SSATernary c t e -> Set.unions [exprUses c, exprUses t, exprUses e]
  SSACall _ args -> Set.unions (map exprUses args)
  SSAInstanceCall obj _ args -> Set.union (exprUses obj) (Set.unions (map exprUses args))
  SSANewObject _ args -> Set.unions (map exprUses args)
  SSAFieldAccess obj _ -> exprUses obj

-- | Convert an SSAVar to a string identifier
varStr :: SSAVar -> String
varStr v = varNameString (ssaName v) ++ "_" ++ show (ssaVersion v)

--------------------------------------------------------------------------------
-- Live Interval Construction
--------------------------------------------------------------------------------

-- | Build live intervals from liveness information.
-- Instructions are numbered linearly in reverse postorder.
buildIntervals :: CFG -> LivenessInfo -> [LiveInterval]
buildIntervals cfg livenessInfo =
  let -- Number instructions linearly
      blockOrder = reversePostorder cfg
      (_, instrNums) = foldl' numberBlock (0, Map.empty) blockOrder

      -- For each variable, find first def and last use
      varRanges = computeVarRanges cfg livenessInfo instrNums blockOrder

  in sortBy (comparing liStart) (Map.elems varRanges)
  where
    numberBlock :: (Int, Map (BlockId, Int) Int) -> BlockId -> (Int, Map (BlockId, Int) Int)
    numberBlock (n, m) bid =
      case getBlock cfg bid of
        Nothing -> (n, m)
        Just block ->
          let numInstrs = length (cfgInstrs block) + 1  -- +1 for terminator
              pairs = [((bid, i), n + i) | i <- [0..numInstrs - 1]]
          in (n + numInstrs, Map.union m (Map.fromList pairs))

-- | Compute the range [start, end] for each variable
computeVarRanges :: CFG -> LivenessInfo -> Map (BlockId, Int) Int -> [BlockId] -> Map String LiveInterval
computeVarRanges cfg livenessInfo instrNums blockOrder =
  let -- Process each block
      ranges = foldl' (processBlock cfg livenessInfo instrNums) Map.empty blockOrder
  in ranges

-- | Process a block to update variable ranges
processBlock :: CFG -> LivenessInfo -> Map (BlockId, Int) Int -> Map String LiveInterval -> BlockId -> Map String LiveInterval
processBlock cfg livenessInfo instrNums ranges bid =
  case getBlock cfg bid of
    Nothing -> ranges
    Just block ->
      let -- Get first and last instruction numbers for this block
          firstInstrNum = Map.findWithDefault 0 (bid, 0) instrNums
          lastInstrNum = Map.findWithDefault 0 (bid, length (cfgInstrs block)) instrNums

          -- Variables live-out extend to end of block
          liveOutVars = Map.findWithDefault Set.empty bid (liveOut livenessInfo)
          ranges' = foldl' (\r v -> updateEnd v lastInstrNum r) ranges (Set.toList liveOutVars)

          -- Variables live-in start at beginning of block
          liveInVars = Map.findWithDefault Set.empty bid (liveIn livenessInfo)
          ranges'' = foldl' (\r v -> updateStart v firstInstrNum r) ranges' (Set.toList liveInVars)

          -- Process instructions for defs and uses
          ranges''' = foldl' (processInstr instrNums bid) ranges'' (zip [0..] (cfgInstrs block))

          -- Process phi defs
          ranges'''' = foldl' (processPhiDef firstInstrNum) ranges''' (cfgPhis block)

          -- Process terminator uses
          termUses = terminatorUses (cfgTerm block)
          ranges''''' = foldl' (\r v -> updateEnd v lastInstrNum r) ranges'''' (Set.toList termUses)

      in ranges'''''

-- | Process an instruction to find definitions and uses
processInstr :: Map (BlockId, Int) Int -> BlockId -> Map String LiveInterval -> (Int, SSAInstr) -> Map String LiveInterval
processInstr instrNums bid ranges (idx, instr) =
  let instrNum = Map.findWithDefault 0 (bid, idx) instrNums
      -- Get uses in this instruction and extend their intervals to this position
      uses = instrUsesSet instr
      rangesWithUses = foldl' (\r v -> updateEnd v instrNum r) ranges (Set.toList uses)
  in case instr of
       SSAAssign var _ ->
         let v = varStr var
         in updateStart v instrNum rangesWithUses
       _ -> rangesWithUses

-- | Process a phi definition
processPhiDef :: Int -> Map String LiveInterval -> PhiNode -> Map String LiveInterval
processPhiDef instrNum ranges phi =
  let v = varStr (phiVar phi)
  in updateStart v instrNum ranges

-- | Update the start of an interval (only if earlier than existing)
updateStart :: String -> Int -> Map String LiveInterval -> Map String LiveInterval
updateStart var pos ranges =
  Map.alter (updateStartMaybe var pos) var ranges

updateStartMaybe :: String -> Int -> Maybe LiveInterval -> Maybe LiveInterval
updateStartMaybe var pos = \case
  Nothing -> Just $ LiveInterval var pos pos
  Just li -> Just $ li { liStart = min (liStart li) pos }

-- | Update the end of an interval (only if later than existing)
updateEnd :: String -> Int -> Map String LiveInterval -> Map String LiveInterval
updateEnd var pos ranges =
  Map.alter (updateEndMaybe var pos) var ranges

updateEndMaybe :: String -> Int -> Maybe LiveInterval -> Maybe LiveInterval
updateEndMaybe var pos = \case
  Nothing -> Just $ LiveInterval var pos pos
  Just li -> Just $ li { liEnd = max (liEnd li) pos }
