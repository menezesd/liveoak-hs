{-# LANGUAGE RecordWildCards #-}

-- | Dataflow optimization orchestration.
-- Splits AST-level simplifications from SSA/CFG-based optimizations.
module LiveOak.DataFlow
  ( optimizeASTDataFlow
  , optimizeSSADataFlow
  ) where

import LiveOak.DataFlow.AST (optimizeASTDataFlow)
import LiveOak.DataFlow.SSA (optimizeSSADataFlow)

