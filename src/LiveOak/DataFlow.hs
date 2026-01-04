-- | Dataflow optimization orchestration.
-- Splits AST-level simplifications from SSA/CFG-based optimizations.
module LiveOak.DataFlow
  ( optimizeASTDataFlow
  ) where

import LiveOak.DataFlow.AST (optimizeASTDataFlow)
