{-# LANGUAGE RecordWildCards #-}

-- | Optimization Pipeline Configuration.
-- Allows enabling/disabling individual optimization passes.
module LiveOak.OptConfig
  ( -- * Configuration
    OptConfig(..)
  , defaultOptConfig
  , aggressiveOptConfig
  , minimalOptConfig

    -- * Pass Flags
  , PassFlags(..)
  , allPassesEnabled
  , noPassesEnabled
  ) where

--------------------------------------------------------------------------------
-- Configuration Types
--------------------------------------------------------------------------------

-- | Individual optimization pass flags
data PassFlags = PassFlags
  { pfSimplifyPhis :: !Bool       -- ^ Simplify phi nodes
  , pfTailCall :: !Bool           -- ^ Tail call optimization
  , pfInline :: !Bool             -- ^ Function inlining
  , pfSCCP :: !Bool               -- ^ Sparse conditional constant propagation
  , pfGVN :: !Bool                -- ^ Global value numbering
  , pfPRE :: !Bool                -- ^ Partial redundancy elimination
  , pfLICM :: !Bool               -- ^ Loop invariant code motion
  , pfStrengthReduce :: !Bool     -- ^ Strength reduction
  , pfCopyProp :: !Bool           -- ^ Copy propagation
  , pfPeephole :: !Bool           -- ^ Peephole optimizations
  , pfDCE :: !Bool                -- ^ Dead code elimination
  , pfDSE :: !Bool                -- ^ Dead store elimination
  , pfSROA :: !Bool               -- ^ Scalar replacement of aggregates
  , pfLoopUnroll :: !Bool         -- ^ Loop unrolling
  , pfJumpThread :: !Bool         -- ^ Jump threading
  , pfSchedule :: !Bool           -- ^ Instruction scheduling
  , pfBlockMerge :: !Bool         -- ^ Block merging
  , pfNullCheck :: !Bool          -- ^ Null check elimination
  , pfDeadArg :: !Bool            -- ^ Dead argument elimination
  , pfReturnProp :: !Bool         -- ^ Return value propagation
  , pfAlgebraic :: !Bool          -- ^ Algebraic simplifications
  , pfReassoc :: !Bool            -- ^ Reassociation
  , pfLoadElim :: !Bool           -- ^ Redundant load elimination
  , pfLCSSA :: !Bool              -- ^ Loop-closed SSA form
  , pfInstCombine :: !Bool        -- ^ Instruction combining
  } deriving (Show, Eq)

-- | Full optimization configuration
data OptConfig = OptConfig
  { ocPasses :: !PassFlags        -- ^ Which passes are enabled
  , ocIterations :: !Int          -- ^ Max pipeline iterations
  , ocInlineThreshold :: !Int     -- ^ Max size for inlining
  , ocUnrollFactor :: !Int        -- ^ Loop unroll factor
  , ocVerbose :: !Bool            -- ^ Verbose output
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Default Configurations
--------------------------------------------------------------------------------

-- | All passes enabled
allPassesEnabled :: PassFlags
allPassesEnabled = PassFlags
  { pfSimplifyPhis = True
  , pfTailCall = True
  , pfInline = True
  , pfSCCP = True
  , pfGVN = True
  , pfPRE = True
  , pfLICM = True
  , pfStrengthReduce = True
  , pfCopyProp = True
  , pfPeephole = True
  , pfDCE = True
  , pfDSE = True
  , pfSROA = True    -- SROA enabled
  , pfLoopUnroll = True   -- Loop unrolling enabled
  , pfJumpThread = True
  , pfSchedule = True
  , pfBlockMerge = True
  , pfNullCheck = True
  , pfDeadArg = True
  , pfReturnProp = True
  , pfAlgebraic = True
  , pfReassoc = True
  , pfLoadElim = True
  , pfLCSSA = True   -- LCSSA ensures loop exits have phis
  , pfInstCombine = True
  }

-- | No passes enabled (for testing)
noPassesEnabled :: PassFlags
noPassesEnabled = PassFlags
  { pfSimplifyPhis = False
  , pfTailCall = False
  , pfInline = False
  , pfSCCP = False
  , pfGVN = False
  , pfPRE = False
  , pfLICM = False
  , pfStrengthReduce = False
  , pfCopyProp = False
  , pfPeephole = False
  , pfDCE = False
  , pfDSE = False
  , pfSROA = False
  , pfLoopUnroll = False
  , pfJumpThread = False
  , pfSchedule = False
  , pfBlockMerge = False
  , pfNullCheck = False
  , pfDeadArg = False
  , pfReturnProp = False
  , pfAlgebraic = False
  , pfReassoc = False
  , pfLoadElim = False
  , pfLCSSA = False
  , pfInstCombine = False
  }

-- | Default optimization configuration
-- Enables safe, well-tested optimizations
defaultOptConfig :: OptConfig
defaultOptConfig = OptConfig
  { ocPasses = allPassesEnabled
  , ocIterations = 3
  , ocInlineThreshold = 50
  , ocUnrollFactor = 4
  , ocVerbose = False
  }

-- | Aggressive optimization configuration
-- Enables all optimizations including experimental ones
aggressiveOptConfig :: OptConfig
aggressiveOptConfig = OptConfig
  { ocPasses = allPassesEnabled
  , ocIterations = 5
  , ocInlineThreshold = 100
  , ocUnrollFactor = 8
  , ocVerbose = False
  }

-- | Minimal optimization configuration
-- Only essential optimizations for fast compilation
minimalOptConfig :: OptConfig
minimalOptConfig = OptConfig
  { ocPasses = PassFlags
      { pfSimplifyPhis = True
      , pfTailCall = False
      , pfInline = False
      , pfSCCP = True
      , pfGVN = False
      , pfPRE = False
      , pfLICM = False
      , pfStrengthReduce = False
      , pfCopyProp = True
      , pfPeephole = True
      , pfDCE = True
      , pfDSE = False
      , pfSROA = False
      , pfLoopUnroll = False
      , pfJumpThread = False
      , pfSchedule = False
      , pfBlockMerge = True   -- Block merging is fast and effective
      , pfNullCheck = False
      , pfDeadArg = False
      , pfReturnProp = False
      , pfAlgebraic = True    -- Algebraic simplifications are cheap
      , pfReassoc = False
      , pfLoadElim = False
      , pfLCSSA = False
      , pfInstCombine = True  -- Instruction combining is cheap
      }
  , ocIterations = 1
  , ocInlineThreshold = 20
  , ocUnrollFactor = 2
  , ocVerbose = False
  }
