{-# LANGUAGE RecordWildCards #-}

-- | SSA-level dataflow orchestration.
-- For now this simply delegates to the safer SSA passes that already
-- exist in the SSA module.
module LiveOak.DataFlow.SSA
  ( optimizeSSADataFlow
  ) where

import LiveOak.Ast (Program)
import LiveOak.Symbol (ProgramSymbols)
import qualified LiveOak.SSA as SSA

-- | Run the SSA optimizations exposed by the SSA module.
optimizeSSADataFlow :: ProgramSymbols -> Program -> Program
optimizeSSADataFlow = SSA.optimizeSSA


