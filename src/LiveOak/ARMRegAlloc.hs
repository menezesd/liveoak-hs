{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Linear scan register allocation for AArch64.
-- Assigns SSA variables to machine registers, with spilling when needed.
module LiveOak.ARMRegAlloc
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

import LiveOak.ARM (ARMReg(..))
import LiveOak.X86Liveness (LiveInterval(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Where a variable lives
data VarLocation
  = InReg !ARMReg    -- ^ Variable is in a register
  | OnStack !Int     -- ^ Variable is on stack at given slot
  deriving (Eq, Show)

-- | Result of register allocation
data RegAllocation = RegAllocation
  { raLocations :: !(Map String VarLocation)  -- ^ Variable -> location
  , raSpillCount :: !Int                      -- ^ Number of spill slots needed
  , raUsedRegs :: !(Set ARMReg)               -- ^ Set of registers actually used
  } deriving (Eq, Show)

-- | Internal state for linear scan
data ScanState = ScanState
  { ssActive :: ![(LiveInterval, ARMReg)]     -- ^ Active intervals (sorted by end)
  , ssFreeRegs :: ![ARMReg]                   -- ^ Available registers
  , ssLocations :: !(Map String VarLocation)  -- ^ Assigned locations
  , ssNextSpill :: !Int                       -- ^ Next spill slot number
  , ssUsedRegs :: !(Set ARMReg)               -- ^ Registers we've allocated
  }

--------------------------------------------------------------------------------
-- Available Registers
--------------------------------------------------------------------------------

-- | Registers available for allocation.
-- Callee-saved (X19-X28): Preserved across calls, good for long-lived values
-- Caller-saved (X9-X15): Must save around calls, good for temporaries
-- Excluded: X0-X8 (args/return), X16-X17 (IP scratch), X18 (platform),
--           X29 (FP), X30 (LR), SP
allocatableRegs :: [ARMReg]
allocatableRegs = [X19, X20, X21, X22, X23, X24, X25, X26, X27, X28,
                   X9, X10, X11, X12, X13, X14, X15]
  -- 17 registers (10 callee-saved + 7 caller-saved)

--------------------------------------------------------------------------------
-- Register Allocation
--------------------------------------------------------------------------------

-- | Perform linear scan register allocation on a set of live intervals.
allocateRegisters :: [LiveInterval] -> RegAllocation
allocateRegisters intervals =
  let sorted = sortBy (comparing liStart) intervals
      initState = ScanState
        { ssActive = []
        , ssFreeRegs = allocatableRegs
        , ssLocations = Map.empty
        , ssNextSpill = 0
        , ssUsedRegs = Set.empty
        }
      finalState = foldl' processInterval initState sorted
  in RegAllocation
       { raLocations = ssLocations finalState
       , raSpillCount = ssNextSpill finalState
       , raUsedRegs = ssUsedRegs finalState
       }

-- | Process a single interval in the linear scan
processInterval :: ScanState -> LiveInterval -> ScanState
processInterval state interval =
  let state' = expireOldIntervals (liStart interval) state
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
    [] -> spillAtInterval state interval
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
    [] -> spillInterval state interval
    active ->
      let (longestLI, longestReg) = last active
      in if liEnd longestLI > liEnd interval
         then let state' = state
                    { ssActive = init active
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
insertByEnd :: (LiveInterval, ARMReg) -> [(LiveInterval, ARMReg)] -> [(LiveInterval, ARMReg)]
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

-- | Callee-saved registers (subset of allocatable)
calleeSavedAlloc :: [ARMReg]
calleeSavedAlloc = [X19, X20, X21, X22, X23, X24, X25, X26, X27, X28]

-- | Get the list of callee-saved registers that were used (need saving in prologue)
usedCalleeRegs :: RegAllocation -> [ARMReg]
usedCalleeRegs alloc =
  filter (`Set.member` raUsedRegs alloc) calleeSavedAlloc
