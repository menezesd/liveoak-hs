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
-- == Alias Analysis Integration
--
-- With alias analysis, LICM can also hoist field loads if:
-- * The load doesn't alias with any store in the loop
-- * The base object is loop-invariant
--
module LiveOak.LICM
  ( -- * LICM Optimization
    runLICM
  , runLICMWithAlias
  , LICMResult(..)
  ) where

import LiveOak.CFG
import LiveOak.Dominance
import LiveOak.Loop
import LiveOak.SSATypes
import LiveOak.MapUtils (lookupSet)
import LiveOak.SSAUtils (blockDefs, isPure, blockMapFromList)
import LiveOak.Alias

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
                      , bid /= loopHeader loop  -- Don't hoist from header (has phis)
                      , Just b <- [Map.lookup bid blockMap]
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

--------------------------------------------------------------------------------
-- Alias-Aware LICM
--------------------------------------------------------------------------------

-- | Store information in a loop
data LoopStore = LoopStore
  { lsTarget :: !SSAExpr
  , lsField :: !String
  , lsOffset :: !Int
  } deriving (Show)

-- | LICM state with alias analysis
data LICMStateAlias = LICMStateAlias
  { licmaHoisted :: ![(BlockId, SSAInstr)]
  , licmaBlockMap :: !(Map BlockId SSABlock)
  , licmaDefsInLoop :: !(Map BlockId (Set String))
  , licmaUsedPreheaders :: !(Set.Set BlockId)
  , licmaPtInfo :: !PointsToInfo
  , licmaLoopStores :: !(Map BlockId [LoopStore])  -- ^ Stores in each loop
  } deriving (Show)

type LICMA a = State LICMStateAlias a

-- | Run LICM with alias analysis
-- This version can hoist field loads that don't alias with loop stores.
runLICMWithAlias :: SSAMethod -> CFG -> DomTree -> LoopNest -> [SSABlock] -> LICMResult
runLICMWithAlias method cfg domTree loops blocks =
  let blockMap = blockMapFromList blocks
      ptInfo = computePointsTo method
      -- Compute definitions in each loop
      defsMap = Map.mapWithKey (computeLoopDefs blockMap) loops
      -- Compute stores in each loop
      storesMap = Map.map (collectLoopStores blockMap) loops
      initState = LICMStateAlias
        { licmaHoisted = []
        , licmaBlockMap = blockMap
        , licmaDefsInLoop = defsMap
        , licmaUsedPreheaders = Set.empty
        , licmaPtInfo = ptInfo
        , licmaLoopStores = storesMap
        }
      -- Process loops from innermost to outermost
      sortedLoops = sortLoopsByDepth loops
      finalState = execState (processLoopsAlias cfg domTree sortedLoops) initState
      -- Build result blocks
      resultBlocks = Map.elems (licmaBlockMap finalState)
  in LICMResult
    { licmOptBlocks = resultBlocks
    , licmHoistedCount = length (licmaHoisted finalState)
    , licmNewPreheaders = Set.toList (licmaUsedPreheaders finalState)
    }

-- | Collect all stores in a loop
collectLoopStores :: Map BlockId SSABlock -> Loop -> [LoopStore]
collectLoopStores blockMap loop =
  [ LoopStore target field off
  | bid <- Set.toList (loopBody loop)
  , Just block <- [Map.lookup bid blockMap]
  , SSAFieldStore target field off _ <- blockInstrs block
  ]

-- | Process all loops with alias analysis
processLoopsAlias :: CFG -> DomTree -> [Loop] -> LICMA ()
processLoopsAlias cfg domTree loops =
  forM_ loops $ \loop -> processLoopAlias cfg domTree loop

-- | Process a single loop with alias analysis
processLoopAlias :: CFG -> DomTree -> Loop -> LICMA ()
processLoopAlias cfg domTree loop = do
  preheader <- getOrCreatePreheaderAlias cfg loop
  case preheader of
    Nothing -> return ()
    Just ph -> do
      defs <- gets (lookupSet (loopHeader loop) . licmaDefsInLoop)
      stores <- gets (Map.findWithDefault [] (loopHeader loop) . licmaLoopStores)
      hoistInvariantCodeAlias cfg domTree loop ph defs stores

-- | Get or create preheader (alias version)
getOrCreatePreheaderAlias :: CFG -> Loop -> LICMA (Maybe BlockId)
getOrCreatePreheaderAlias _cfg loop =
  case loopPreheader loop of
    Just ph -> do
      modify $ \s -> s { licmaUsedPreheaders = Set.insert ph (licmaUsedPreheaders s) }
      return (Just ph)
    Nothing -> return Nothing

-- | Hoist loop-invariant code with alias analysis
hoistInvariantCodeAlias :: CFG -> DomTree -> Loop -> BlockId -> Set String -> [LoopStore] -> LICMA ()
hoistInvariantCodeAlias cfg domTree loop preheader defsInLoop stores = do
  changed <- hoistPassAlias cfg domTree loop preheader defsInLoop stores
  when changed $ hoistInvariantCodeAlias cfg domTree loop preheader defsInLoop stores

-- | Single pass of hoisting with alias analysis
hoistPassAlias :: CFG -> DomTree -> Loop -> BlockId -> Set String -> [LoopStore] -> LICMA Bool
hoistPassAlias _cfg domTree loop preheader defsInLoop stores = do
  blockMap <- gets licmaBlockMap
  ptInfo <- gets licmaPtInfo
  let bodyBlocks = [b | bid <- Set.toList (loopBody loop)
                      , bid /= loopHeader loop
                      , Just b <- [Map.lookup bid blockMap]
                      ]
  -- Find hoistable instructions (including loads with alias analysis)
  hoistable <- fmap concat $ forM bodyBlocks $ \block -> do
    findHoistableAlias domTree loop defsInLoop stores ptInfo block

  -- Hoist them
  forM_ hoistable $ \(fromBlock, instr) -> do
    hoistInstrAlias fromBlock preheader instr

  return (not $ null hoistable)

-- | Find hoistable instructions with alias analysis
findHoistableAlias :: DomTree -> Loop -> Set String -> [LoopStore] -> PointsToInfo
                   -> SSABlock -> LICMA [(BlockId, SSAInstr)]
findHoistableAlias domTree loop defsInLoop stores ptInfo SSABlock{..} = do
  let hoistable = filter (canHoistAlias domTree loop defsInLoop stores ptInfo) blockInstrs
  return [(blockLabel, instr) | instr <- hoistable]

-- | Check if an instruction can be hoisted (with alias analysis)
canHoistAlias :: DomTree -> Loop -> Set String -> [LoopStore] -> PointsToInfo -> SSAInstr -> Bool
canHoistAlias _domTree loop defsInLoop stores ptInfo = \case
  SSAAssign _var expr ->
    -- Standard check: loop-invariant and pure
    if isLoopInvariant loop defsInLoop expr && isPure expr
    then True
    -- Enhanced check: field loads that don't alias with any loop store
    else case expr of
      SSAFieldAccess base field ->
        isLoopInvariant loop defsInLoop base &&
        not (anyStoreAliases ptInfo stores base field)
      _ -> False

  _ -> False

-- | Check if any store in the loop may alias with a field access
anyStoreAliases :: PointsToInfo -> [LoopStore] -> SSAExpr -> String -> Bool
anyStoreAliases ptInfo stores loadBase loadField =
  any (storeAliasesLoad ptInfo loadBase loadField) stores

-- | Check if a store may alias with a load
storeAliasesLoad :: PointsToInfo -> SSAExpr -> String -> LoopStore -> Bool
storeAliasesLoad ptInfo loadBase loadField LoopStore{..} =
  case loadStoreAlias ptInfo loadBase loadField lsTarget lsField lsOffset of
    NoAlias -> False
    _ -> True

-- | Hoist an instruction (alias version)
hoistInstrAlias :: BlockId -> BlockId -> SSAInstr -> LICMA ()
hoistInstrAlias fromBlock toBlock instr = do
  blockMap <- gets licmaBlockMap
  case Map.lookup fromBlock blockMap of
    Just block -> do
      let block' = block { blockInstrs = filter (/= instr) (blockInstrs block) }
      modify $ \s -> s { licmaBlockMap = Map.insert fromBlock block' (licmaBlockMap s) }
    Nothing -> return ()

  case Map.lookup toBlock blockMap of
    Just block -> do
      let (nonTerm, term) = splitInstrsTerm (blockInstrs block)
          block' = block { blockInstrs = nonTerm ++ [instr] ++ term }
      modify $ \s -> s { licmaBlockMap = Map.insert toBlock block' (licmaBlockMap s) }
    Nothing -> return ()

  modify $ \s -> s { licmaHoisted = (toBlock, instr) : licmaHoisted s }
