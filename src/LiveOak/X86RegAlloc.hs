{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Linear scan register allocation for x86_64.
-- Assigns SSA variables to machine registers, with spilling when needed.
module LiveOak.X86RegAlloc
  ( -- * Types
    RegAllocation(..)
  , VarLocation(..)

    -- * Register Allocation
  , allocateRegisters
  , allocatableRegs

    -- * Queries
  , getVarLocation
  , usedCalleeRegs
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (sortBy, foldl')
import Data.Ord (comparing)

import LiveOak.X86 (X86Reg(..))
import LiveOak.X86Liveness (LiveInterval(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Where a variable lives
data VarLocation
  = InReg !X86Reg    -- ^ Variable is in a register
  | OnStack !Int     -- ^ Variable is on stack at given slot
  deriving (Eq, Show)

-- | Result of register allocation
data RegAllocation = RegAllocation
  { raLocations :: !(Map String VarLocation)  -- ^ Variable -> location
  , raSpillCount :: !Int                      -- ^ Number of spill slots needed
  , raUsedRegs :: !(Set X86Reg)               -- ^ Set of registers actually used
  } deriving (Eq, Show)

-- | Internal state for linear scan
data ScanState = ScanState
  { ssActive :: ![(LiveInterval, X86Reg)]     -- ^ Active intervals (sorted by end)
  , ssFreeRegs :: ![X86Reg]                   -- ^ Available registers
  , ssLocations :: !(Map String VarLocation)  -- ^ Assigned locations
  , ssNextSpill :: !Int                       -- ^ Next spill slot number
  , ssUsedRegs :: !(Set X86Reg)               -- ^ Registers we've allocated
  }

--------------------------------------------------------------------------------
-- Available Registers
--------------------------------------------------------------------------------

-- | Registers available for allocation.
-- We use callee-saved registers so we don't need to save/restore around every call.
-- This simplifies code but requires saving them in prologue if used.
allocatableRegs :: [X86Reg]
allocatableRegs = [RBX, R12, R13, R14, R15]  -- 5 callee-saved registers

--------------------------------------------------------------------------------
-- Register Allocation
--------------------------------------------------------------------------------

-- | Perform linear scan register allocation on a set of live intervals.
-- Returns the allocation result with variable locations and spill info.
allocateRegisters :: [LiveInterval] -> RegAllocation
allocateRegisters intervals =
  let -- Sort intervals by start position
      sorted = sortBy (comparing liStart) intervals

      -- Initial state with all registers free
      initState = ScanState
        { ssActive = []
        , ssFreeRegs = allocatableRegs
        , ssLocations = Map.empty
        , ssNextSpill = 0
        , ssUsedRegs = Set.empty
        }

      -- Run linear scan
      finalState = foldl' processInterval initState sorted

  in RegAllocation
       { raLocations = ssLocations finalState
       , raSpillCount = ssNextSpill finalState
       , raUsedRegs = ssUsedRegs finalState
       }

-- | Process a single interval in the linear scan
processInterval :: ScanState -> LiveInterval -> ScanState
processInterval state interval =
  let -- Expire old intervals (those that have ended)
      state' = expireOldIntervals (liStart interval) state

      -- Check if variable is already assigned (e.g., from phi resolution)
      alreadyAssigned = Map.member (liVar interval) (ssLocations state')

  in if alreadyAssigned
     then state'
     else if null (ssFreeRegs state')
          then spillAtInterval state' interval
          else assignRegister state' interval

-- | Expire intervals that have ended before the current position
expireOldIntervals :: Int -> ScanState -> ScanState
expireOldIntervals pos state =
  let (expired, remaining) = span (\(li, _) -> liEnd li < pos) (ssActive state)
      freedRegs = [reg | (_, reg) <- expired]
  in state
       { ssActive = remaining
       , ssFreeRegs = freedRegs ++ ssFreeRegs state
       }

-- | Assign a register to an interval
assignRegister :: ScanState -> LiveInterval -> ScanState
assignRegister state interval =
  case ssFreeRegs state of
    [] ->
      -- No free registers - fall back to spilling (defensive, should not happen
      -- since caller checks ssFreeRegs, but better than crashing)
      spillAtInterval state interval
    (reg:rest) ->
      let newActive = insertByEnd (interval, reg) (ssActive state)
      in state
           { ssActive = newActive
           , ssFreeRegs = rest
           , ssLocations = Map.insert (liVar interval) (InReg reg) (ssLocations state)
           , ssUsedRegs = Set.insert reg (ssUsedRegs state)
           }

-- | Spill either the current interval or an active one
spillAtInterval :: ScanState -> LiveInterval -> ScanState
spillAtInterval state interval =
  case ssActive state of
    [] ->
      -- No active intervals, spill the current one
      spillInterval state interval

    active ->
      let (longestLI, longestReg) = last active
      in if liEnd longestLI > liEnd interval
         -- Spill the longest active interval, give its register to current
         then let state' = state
                    { ssActive = init active  -- Remove longest
                    , ssLocations = Map.insert (liVar longestLI)
                                               (OnStack (ssNextSpill state))
                                               (ssLocations state)
                    , ssNextSpill = ssNextSpill state + 1
                    }
                  newActive = insertByEnd (interval, longestReg) (ssActive state')
              in state'
                   { ssActive = newActive
                   , ssLocations = Map.insert (liVar interval)
                                              (InReg longestReg)
                                              (ssLocations state')
                   }
         -- Spill current interval
         else spillInterval state interval

-- | Spill an interval to the stack
spillInterval :: ScanState -> LiveInterval -> ScanState
spillInterval state interval =
  state
    { ssLocations = Map.insert (liVar interval)
                               (OnStack (ssNextSpill state))
                               (ssLocations state)
    , ssNextSpill = ssNextSpill state + 1
    }

-- | Insert interval into active list, maintaining sorted order by end position
insertByEnd :: (LiveInterval, X86Reg) -> [(LiveInterval, X86Reg)] -> [(LiveInterval, X86Reg)]
insertByEnd item@(li, _) = go
  where
    go [] = [item]
    go (x@(xli, _):xs)
      | liEnd li <= liEnd xli = item : x : xs
      | otherwise = x : go xs

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Get the location of a variable from the allocation
getVarLocation :: String -> RegAllocation -> Maybe VarLocation
getVarLocation var alloc = Map.lookup var (raLocations alloc)

-- | Get the list of callee-saved registers that were used (need to be saved in prologue)
usedCalleeRegs :: RegAllocation -> [X86Reg]
usedCalleeRegs alloc =
  filter (`Set.member` raUsedRegs alloc) allocatableRegs
