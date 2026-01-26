{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Stack Allocation for Non-Escaping Objects.
-- Objects that don't escape their allocating method can be stack-allocated
-- instead of heap-allocated, avoiding GC pressure.
--
-- == Benefits
-- - No heap allocation overhead
-- - No garbage collection needed
-- - Better cache locality
-- - Automatic deallocation on function return
--
-- == Requirements
-- - Object must not escape (verified by escape analysis)
-- - Object size must be known at compile time
-- - Object lifetime must be bounded by function scope
--
module LiveOak.StackAlloc
  ( -- * Stack Allocation
    promoteToStack
  , StackAllocResult(..)

    -- * Analysis
  , StackCandidate(..)
  , findStackCandidates
  ) where

import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Escape (analyzeMethodEscape, EscapeResult(..), isNonEscaping)
import LiveOak.Symbol (ProgramSymbols, lookupClass, csFieldOrder)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Stack allocation result
data StackAllocResult = StackAllocResult
  { saOptBlocks :: ![SSABlock]
  , saPromoted :: !Int               -- ^ Number of allocations promoted
  , saSavedBytes :: !Int             -- ^ Estimated heap bytes saved
  } deriving (Show)

-- | Candidate for stack allocation
data StackCandidate = StackCandidate
  { scVar :: !String                 -- ^ Variable holding the object
  , scClass :: !String               -- ^ Class being instantiated
  , scBlock :: !BlockId              -- ^ Block where allocation occurs
  , scSize :: !Int                   -- ^ Size in bytes
  } deriving (Show)

--------------------------------------------------------------------------------
-- Stack Allocation Promotion
--------------------------------------------------------------------------------

-- | Promote non-escaping allocations to stack
promoteToStack :: ProgramSymbols -> SSAMethod -> StackAllocResult
promoteToStack syms method =
  let blocks = ssaMethodBlocks method
      -- Run escape analysis
      escapeInfo = analyzeMethodEscape method
      -- Find stack allocation candidates
      candidates = findStackCandidates syms escapeInfo blocks
      -- Apply transformation
      (optimized, count, saved) = applyStackAlloc syms candidates blocks
  in StackAllocResult
    { saOptBlocks = optimized
    , saPromoted = count
    , saSavedBytes = saved
    }

--------------------------------------------------------------------------------
-- Candidate Detection
--------------------------------------------------------------------------------

-- | Find allocations that can be stack-allocated
findStackCandidates :: ProgramSymbols -> EscapeResult -> [SSABlock] -> [StackCandidate]
findStackCandidates syms escapeInfo = concatMap (findBlockCandidates syms escapeInfo)

-- | Find candidates in a block
findBlockCandidates :: ProgramSymbols -> EscapeResult -> SSABlock -> [StackCandidate]
findBlockCandidates syms escapeInfo SSABlock{..} =
  mapMaybe (analyzeAlloc syms escapeInfo blockLabel) blockInstrs

-- | Analyze an allocation instruction
analyzeAlloc :: ProgramSymbols -> EscapeResult -> BlockId -> SSAInstr -> Maybe StackCandidate
analyzeAlloc syms escapeInfo bid = \case
  SSAAssign var (SSANewObject className _) ->
    let varName = varNameString (ssaName var)
    in if isNonEscaping escapeInfo varName
       then case computeObjectSize syms className of
         Just size -> Just $ StackCandidate varName className bid size
         Nothing -> Nothing
       else Nothing
  _ -> Nothing

-- | Compute object size from class definition
computeObjectSize :: ProgramSymbols -> String -> Maybe Int
computeObjectSize syms className =
  case lookupClass className syms of
    Just cs ->
      let numFields = length (csFieldOrder cs)
          -- Each field is 8 bytes (pointer-sized)
          size = numFields * 8
      in Just size
    Nothing -> Nothing

--------------------------------------------------------------------------------
-- Stack Allocation Transformation
--------------------------------------------------------------------------------

-- | Apply stack allocation transformation
applyStackAlloc :: ProgramSymbols -> [StackCandidate] -> [SSABlock] -> ([SSABlock], Int, Int)
applyStackAlloc syms candidates blocks =
  let -- Build set of variables to stack-allocate
      stackVars = Set.fromList [scVar c | c <- candidates]
      -- Transform blocks
      optimized = map (transformBlock syms stackVars) blocks
      -- Calculate stats
      count = length candidates
      saved = sum [scSize c | c <- candidates]
  in (optimized, count, saved)

-- | Transform a block for stack allocation
transformBlock :: ProgramSymbols -> Set String -> SSABlock -> SSABlock
transformBlock syms stackVars block@SSABlock{..} =
  block { blockInstrs = map (transformInstr syms stackVars) blockInstrs }

-- | Transform an instruction
transformInstr :: ProgramSymbols -> Set String -> SSAInstr -> SSAInstr
transformInstr syms stackVars = \case
  -- Replace heap allocation with stack allocation marker
  SSAAssign var (SSANewObject className args)
    | Set.member (varNameString (ssaName var)) stackVars ->
        -- Mark as stack-allocated by using a special call
        -- In actual codegen, this would allocate on stack instead of calling malloc
        SSAAssign var (SSACall "__stack_alloc" [SSAInt (objectSize syms className), SSAStr className])

  other -> other
  where
    objectSize s cn = case computeObjectSize s cn of
      Just size -> size
      Nothing -> 0

--------------------------------------------------------------------------------
-- Code Generation Support
--------------------------------------------------------------------------------

-- | Information for code generator about stack allocations
data StackAllocInfo = StackAllocInfo
  { saiVars :: !(Set String)         -- ^ Variables to stack-allocate
  , saiSizes :: !(Map String Int)    -- ^ Size of each allocation
  , saiOffsets :: !(Map String Int)  -- ^ Stack offset for each allocation
  } deriving (Show)

-- | Compute stack layout for allocations
computeStackLayout :: [StackCandidate] -> Int -> StackAllocInfo
computeStackLayout candidates baseOffset =
  let (vars, sizes, offsets, _) = foldl' addCandidate
        (Set.empty, Map.empty, Map.empty, baseOffset) candidates
  in StackAllocInfo vars sizes offsets
  where
    addCandidate (vs, szs, offs, off) StackCandidate{..} =
      let newOff = off + scSize
      in (Set.insert scVar vs,
          Map.insert scVar scSize szs,
          Map.insert scVar off offs,
          newOff)
