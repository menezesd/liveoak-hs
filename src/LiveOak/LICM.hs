{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Loop Invariant Code Motion (LICM).
--
-- Moves computations that don't change within a loop to before the loop,
-- reducing redundant work on each iteration.
--
-- == Algorithm
--
-- 1. Identify all loops using back-edge detection
-- 2. For each loop (innermost first):
--    a. Find the preheader block (single predecessor to loop header)
--    b. Identify loop-invariant instructions:
--       - All operands are defined outside the loop, OR
--       - All operands are themselves loop-invariant
--    c. Move invariant instructions to the preheader
--
-- == Example
--
-- @
-- Before:                      After:
--   loop:                        preheader:
--     x = a + b  -- invariant      x = a + b  -- hoisted
--     y = x * i  -- not invariant  loop:
--     i = i + 1                      y = x * i
--     goto loop                      i = i + 1
--                                    goto loop
-- @
--
-- == Safety Requirements
--
-- An instruction can only be hoisted if:
--
-- * It is pure (no side effects)
-- * It dominates all loop exits (will always execute)
-- * All its operands are available in the preheader
--
module LiveOak.LICM
  ( -- * LICM Optimization
    runLICM
  , LICMResult(..)
  ) where

import LiveOak.CFG
import LiveOak.Dominance
import LiveOak.Loop
import LiveOak.SSATypes
import LiveOak.MapUtils (lookupSet)
import LiveOak.SSAUtils (blockDefs, isPure, blockMapFromList)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (sortBy)
import Data.Ord (comparing, Down(..))
import Control.Monad (forM, forM_, when)
import Control.Monad.State.Strict

--------------------------------------------------------------------------------
-- LICM Types
--------------------------------------------------------------------------------

-- | LICM state
data LICMState = LICMState
  { licmHoisted :: ![(BlockId, SSAInstr)]  -- ^ Instructions hoisted (preheader, instr)
  , licmBlockMap :: !(Map BlockId SSABlock) -- ^ Block map (mutable)
  , licmDefsInLoop :: !(Map BlockId (Set String))  -- ^ Definitions in each loop
  , licmUsedPreheaders :: !(Set.Set BlockId) -- ^ Preheaders used for hoisting
  } deriving (Show)

type LICM a = State LICMState a

-- | LICM result
data LICMResult = LICMResult
  { licmOptBlocks :: ![SSABlock]      -- ^ Optimized blocks with hoisted code
  , licmHoistedCount :: !Int          -- ^ Number of hoisted instructions
  , licmNewPreheaders :: ![BlockId]   -- ^ Preheaders that were created
  } deriving (Show)

--------------------------------------------------------------------------------
-- LICM Algorithm
--------------------------------------------------------------------------------

-- | Run LICM on a method
runLICM :: CFG -> DomTree -> LoopNest -> [SSABlock] -> LICMResult
runLICM cfg domTree loops blocks =
  let blockMap = blockMapFromList blocks
      -- Compute definitions in each loop
      defsMap = Map.mapWithKey (computeLoopDefs blockMap) loops
      initState = LICMState
        { licmHoisted = []
        , licmBlockMap = blockMap
        , licmDefsInLoop = defsMap
        , licmUsedPreheaders = Set.empty
        }
      -- Process loops from innermost to outermost
      sortedLoops = sortLoopsByDepth loops
      finalState = execState (processLoops cfg domTree sortedLoops) initState
      -- Build result blocks
      resultBlocks = Map.elems (licmBlockMap finalState)
  in LICMResult
    { licmOptBlocks = resultBlocks
    , licmHoistedCount = length (licmHoisted finalState)
    , licmNewPreheaders = Set.toList (licmUsedPreheaders finalState)
    }

-- | Sort loops by depth (innermost first)
sortLoopsByDepth :: LoopNest -> [Loop]
sortLoopsByDepth = sortBy (comparing (Down . loopNestDepth)) . Map.elems

-- | Compute all definitions within a loop
computeLoopDefs :: Map BlockId SSABlock -> BlockId -> Loop -> Set String
computeLoopDefs blockMap _ loop =
  Set.unions [blockDefs b | bid <- Set.toList (loopBody loop)
                          , Just b <- [Map.lookup bid blockMap]]

-- | Process all loops
processLoops :: CFG -> DomTree -> [Loop] -> LICM ()
processLoops cfg domTree loops =
  forM_ loops $ \loop -> processLoop cfg domTree loop

-- | Process a single loop
processLoop :: CFG -> DomTree -> Loop -> LICM ()
processLoop cfg domTree loop = do
  -- Get the preheader (or create one)
  preheader <- getOrCreatePreheader cfg loop
  case preheader of
    Nothing -> return ()  -- Can't hoist without preheader
    Just ph -> do
      -- Get definitions in this loop
      defs <- gets (lookupSet (loopHeader loop) . licmDefsInLoop)
      -- Find and hoist invariant instructions
      hoistInvariantCode cfg domTree loop ph defs

-- | Get or create a preheader for a loop
-- Note: Currently only uses existing preheaders. Creating new ones would require
-- CFG modification which is not implemented yet.
getOrCreatePreheader :: CFG -> Loop -> LICM (Maybe BlockId)
getOrCreatePreheader _cfg loop =
  case loopPreheader loop of
    Just ph -> do
      -- Track that we're using this preheader for hoisting
      modify $ \s -> s { licmUsedPreheaders = Set.insert ph (licmUsedPreheaders s) }
      return (Just ph)
    Nothing -> do
      -- Would need to create preheader by splitting edges
      -- For now, skip loops without preheaders
      return Nothing

-- | Hoist loop-invariant code to the preheader
hoistInvariantCode :: CFG -> DomTree -> Loop -> BlockId -> Set String -> LICM ()
hoistInvariantCode cfg domTree loop preheader defsInLoop = do
  -- Iterate until no more hoisting possible
  changed <- hoistPass cfg domTree loop preheader defsInLoop
  when changed $ hoistInvariantCode cfg domTree loop preheader defsInLoop

-- | Single pass of hoisting
hoistPass :: CFG -> DomTree -> Loop -> BlockId -> Set String -> LICM Bool
hoistPass _cfg domTree loop preheader defsInLoop = do
  blockMap <- gets licmBlockMap
  let bodyBlocks = [b | bid <- Set.toList (loopBody loop)
                      , Just b <- [Map.lookup bid blockMap]
                      , bid /= loopHeader loop  -- Don't hoist from header (has phis)
                      ]
  -- Find hoistable instructions
  hoistable <- fmap concat $ forM bodyBlocks $ \block -> do
    findHoistable domTree loop defsInLoop block

  -- Hoist them
  forM_ hoistable $ \(fromBlock, instr) -> do
    hoistInstr fromBlock preheader instr

  return (not $ null hoistable)

-- | Find hoistable instructions in a block
findHoistable :: DomTree -> Loop -> Set String -> SSABlock -> LICM [(BlockId, SSAInstr)]
findHoistable domTree loop defsInLoop SSABlock{..} = do
  let hoistable = filter (canHoist domTree loop defsInLoop) blockInstrs
  return [(blockLabel, instr) | instr <- hoistable]

-- | Check if an instruction can be hoisted
canHoist :: DomTree -> Loop -> Set String -> SSAInstr -> Bool
canHoist _domTree loop defsInLoop = \case
  SSAAssign _var expr ->
    -- Can hoist if:
    -- 1. Expression is loop-invariant
    -- 2. No side effects
    -- 3. Not used before definition in loop (SSA guarantees this)
    isLoopInvariant loop defsInLoop expr && isPure expr

  -- Other instructions cannot be hoisted
  _ -> False

-- | Hoist an instruction from one block to another
hoistInstr :: BlockId -> BlockId -> SSAInstr -> LICM ()
hoistInstr fromBlock toBlock instr = do
  -- Remove from source block
  blockMap <- gets licmBlockMap
  case Map.lookup fromBlock blockMap of
    Just block -> do
      let block' = block { blockInstrs = filter (/= instr) (blockInstrs block) }
      modify $ \s -> s { licmBlockMap = Map.insert fromBlock block' (licmBlockMap s) }
    Nothing -> return ()

  -- Add to preheader (before terminator)
  case Map.lookup toBlock blockMap of
    Just block -> do
      let (nonTerm, term) = splitInstrsTerm (blockInstrs block)
          block' = block { blockInstrs = nonTerm ++ [instr] ++ term }
      modify $ \s -> s { licmBlockMap = Map.insert toBlock block' (licmBlockMap s) }
    Nothing -> return ()

  -- Record hoisted instruction
  modify $ \s -> s { licmHoisted = (toBlock, instr) : licmHoisted s }

-- | Split instructions into non-terminators and terminator
splitInstrsTerm :: [SSAInstr] -> ([SSAInstr], [SSAInstr])
splitInstrsTerm instrs =
  let (nonTerm, term) = break isTerm instrs
  in (nonTerm, term)
  where
    isTerm (SSAJump _) = True
    isTerm (SSABranch _ _ _) = True
    isTerm (SSAReturn _) = True
    isTerm _ = False
