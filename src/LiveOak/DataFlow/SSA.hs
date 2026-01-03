{-# LANGUAGE RecordWildCards #-}

-- | SSA-level dataflow orchestration.
-- For now this simply delegates to the safer SSA passes that already
-- exist in the SSA module.
module LiveOak.DataFlow.SSA
  ( optimizeSSADataFlow
  ) where

import LiveOak.Ast (Program)
import qualified LiveOak.SSA as SSA

-- | Run the SSA optimizations exposed by the SSA module.
optimizeSSADataFlow :: Program -> Program
optimizeSSADataFlow =
    SSA.fullSSAOptimize
  . SSA.structuredSSAOpt

