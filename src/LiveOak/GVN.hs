{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Global Value Numbering (GVN).
-- Eliminates redundant computations by identifying expressions that
-- compute the same value across basic blocks.
module LiveOak.GVN
  ( -- * GVN Optimization
    runGVN
  , GVNResult(..)
  ) where

import LiveOak.CFG
import LiveOak.Dominance
import LiveOak.SSATypes (SSABlock(..), SSAInstr(..), SSAExpr(..), PhiNode(..), SSAVar(..), VarKey, varKey, varFromKey)
import LiveOak.Ast (BinaryOp(..), UnaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (sortOn)
import Control.Monad (forM, foldM)
import Control.Monad.State.Strict

--------------------------------------------------------------------------------
-- Value Numbering Types
--------------------------------------------------------------------------------

-- | Value number
type ValueNum = Int

-- | Expression key for value numbering (normalized form)

data ExprKey
  = KeyInt !Int
  | KeyBool !Bool
  | KeyNull
  | KeyStr !String
  | KeyVar !VarKey            -- Variable use
  | KeyUnary !UnaryOp !ValueNum
  | KeyBinary !BinaryOp !ValueNum !ValueNum
  | KeyPhi ![(BlockId, ValueNum)] -- Phi with (predecessor, value number)
  | KeyCall !String ![ValueNum]  -- Function call (not memoized)
  deriving (Eq, Ord, Show)

-- | GVN state
data GVNState = GVNState
  { gvnNextNum :: !ValueNum                   -- ^ Next available value number
  , gvnExprToNum :: !(Map ExprKey ValueNum)   -- ^ Expression -> value number
  , gvnVarToNum :: !(Map VarKey ValueNum)     -- ^ Variable -> its value number
  , gvnNumToExpr :: !(Map ValueNum SSAExpr)   -- ^ Value number -> canonical expression
  , gvnNumToVar :: !(Map ValueNum VarKey)     -- ^ Value number -> canonical variable
  , gvnReplacements :: !(Map VarKey VarKey)   -- ^ Variable -> replacement variable
  , gvnAllReplacements :: !(Map VarKey VarKey) -- ^ All replacements (global)
  , gvnElimCount :: !Int                      -- ^ Count of eliminated expressions
  } deriving (Show)

type GVN a = State GVNState a

-- | Initial GVN state
initGVNState :: GVNState
initGVNState = GVNState
  { gvnNextNum = 0
  , gvnExprToNum = Map.empty
  , gvnVarToNum = Map.empty
  , gvnNumToExpr = Map.empty
  , gvnNumToVar = Map.empty
  , gvnReplacements = Map.empty
  , gvnAllReplacements = Map.empty
  , gvnElimCount = 0
  }

--------------------------------------------------------------------------------
-- GVN Algorithm
--------------------------------------------------------------------------------

-- | Result of GVN analysis
data GVNResult = GVNResult
  { gvnOptBlocks :: ![SSABlock]              -- ^ Optimized blocks
  , gvnEliminated :: !Int                    -- ^ Number of eliminated expressions
  , gvnReplacementMap :: !(Map VarKey VarKey) -- ^ Replacements made
  } deriving (Show)

-- | Run GVN on a method
runGVN :: CFG -> DomTree -> [SSABlock] -> GVNResult
runGVN cfg domTree blocks =
  let blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      runner = if hasBackEdge cfg domTree
               then processBlockTreeLocal
               else processBlockTree
      (optimized, finalState) =
        runState (runner blockMap domTree (cfgEntry cfg)) initGVNState
  in GVNResult
    { gvnOptBlocks = optimized
    , gvnEliminated = gvnElimCount finalState
    , gvnReplacementMap = gvnAllReplacements finalState
    }

hasBackEdge :: CFG -> DomTree -> Bool
hasBackEdge cfg domTree =
  any isBackEdge [(from, to) | from <- allBlockIds cfg, to <- successors cfg from]
  where
    isBackEdge (from, to) = dominates domTree to from

-- | Process blocks in dominator tree order with scoped state.
-- Definitions in a block are visible to dominated children, but not siblings.
processBlockTree :: Map BlockId SSABlock -> DomTree -> BlockId -> GVN [SSABlock]
processBlockTree blockMap domTree bid = do
  stBefore <- get
  case Map.lookup bid blockMap of
    Nothing -> return []
    Just block -> do
      block' <- processBlock block
      stAfter <- get
      let children = domChildren domTree bid
      (childBlocks, stGlobal) <- foldM (processChild blockMap domTree stAfter)
                                            ([], stAfter)
                                            children
      let stRestore = mergeScopedState stBefore stGlobal
      put stRestore
      return (block' : childBlocks)

processBlockTreeLocal :: Map BlockId SSABlock -> DomTree -> BlockId -> GVN [SSABlock]
processBlockTreeLocal blockMap domTree bid = do
  stBefore <- get
  let baseState = resetLocalState stBefore
  put baseState
  case Map.lookup bid blockMap of
    Nothing -> do
      put stBefore
      return []
    Just block -> do
      block' <- processBlock block
      stAfter <- get
      let baseForChild = resetLocalState stAfter
          children = domChildren domTree bid
      (childBlocks, stGlobal) <- foldM (processChildLocal blockMap domTree baseForChild)
                                            ([], baseForChild)
                                            children
      let stRestore = mergeScopedState stBefore stGlobal
      put stRestore
      return (block' : childBlocks)

mergeScopedState :: GVNState -> GVNState -> GVNState
mergeScopedState scoped global = scoped
  { gvnNextNum = gvnNextNum global
  , gvnAllReplacements = gvnAllReplacements global
  , gvnElimCount = gvnElimCount global
  }

processChild :: Map BlockId SSABlock -> DomTree -> GVNState -> ([SSABlock], GVNState) -> BlockId
             -> GVN ([SSABlock], GVNState)
processChild blockMap domTree baseState (acc, stGlobal) childId = do
  put (mergeScopedState baseState stGlobal)
  blocks' <- processBlockTree blockMap domTree childId
  stAfter <- get
  return (acc ++ blocks', stAfter)

processChildLocal :: Map BlockId SSABlock -> DomTree -> GVNState -> ([SSABlock], GVNState) -> BlockId
                  -> GVN ([SSABlock], GVNState)
processChildLocal blockMap domTree baseState (acc, stGlobal) childId = do
  put (mergeScopedState baseState stGlobal)
  blocks' <- processBlockTreeLocal blockMap domTree childId
  stAfter <- get
  return (acc ++ blocks', stAfter)

resetLocalState :: GVNState -> GVNState
resetLocalState st = st
  { gvnExprToNum = Map.empty
  , gvnVarToNum = Map.empty
  , gvnNumToVar = Map.empty
  , gvnReplacements = Map.empty
  }

-- | Process a single block
processBlock :: SSABlock -> GVN SSABlock
processBlock SSABlock{..} = do
  -- Process phi nodes
  phis' <- mapM processPhi blockPhis
  -- Process instructions
  instrs' <- mapM processInstr blockInstrs
  return SSABlock
    { blockLabel = blockLabel
    , blockPhis = phis'
    , blockInstrs = instrs'
    }

-- | Process a phi node
processPhi :: PhiNode -> GVN PhiNode
processPhi phi@PhiNode{..} = do
  -- Get value numbers for all arguments
  argNums <- forM phiArgs $ \(predId, argVar) -> do
    getOrCreateVarNum (varKey argVar)
      >>= \num -> return (predId, num)
  let argNums' = sortOn fst argNums
  -- Create phi key
  let key = KeyPhi argNums'
  -- Check if we've seen this phi before
  existing <- gets (Map.lookup key . gvnExprToNum)
  case existing of
    Just num -> do
      -- This phi computes the same value as another expression
      existingVar <- gets (Map.lookup num . gvnNumToVar)
      case existingVar of
        Just v | v /= varKey phiVar -> do
          -- Replace this variable with the existing one
          recordReplacement (varKey phiVar) v
          -- But still assign the same value number
          setVarNum (varKey phiVar) num
        _ -> setVarNum (varKey phiVar) num
    Nothing -> do
      -- New value - assign fresh number
      num <- freshValueNum
      recordExpr key num (SSAUse phiVar)
      setVarNum (varKey phiVar) num
  return phi

-- | Process an instruction
processInstr :: SSAInstr -> GVN SSAInstr
processInstr = \case
  SSAAssign var expr -> do
    -- Value number the expression
    (expr', num) <- valueNumberExpr expr
    -- Check if we can replace with existing variable
    existingVar <- gets (Map.lookup num . gvnNumToVar)
    case existingVar of
      Just v | v /= varKey var -> do
        -- This computes the same value as v
        recordReplacement (varKey var) v
        setVarNum (varKey var) num
        -- Keep the assignment but mark it for potential DCE
        return $ SSAAssign var expr'
      _ -> do
        setVarNum (varKey var) num
        -- Record this as the canonical variable for this value number
        modify $ \s -> s { gvnNumToVar = Map.insert num (varKey var) (gvnNumToVar s) }
        return $ SSAAssign var expr'

  SSAReturn mexpr -> do
    mexpr' <- traverse (fmap fst . valueNumberExpr) mexpr
    return $ SSAReturn mexpr'

  SSABranch cond thenB elseB -> do
    (cond', _) <- valueNumberExpr cond
    return $ SSABranch cond' thenB elseB

  SSAJump target ->
    return $ SSAJump target

  SSAFieldStore target field off value -> do
    (target', _) <- valueNumberExpr target
    (value', _) <- valueNumberExpr value
    return $ SSAFieldStore target' field off value'

  SSAExprStmt expr -> do
    (expr', _) <- valueNumberExpr expr
    return $ SSAExprStmt expr'

-- | Value number an expression, returning optimized expression and its value number
valueNumberExpr :: SSAExpr -> GVN (SSAExpr, ValueNum)
valueNumberExpr expr = case expr of
  SSAInt n -> do
    let key = KeyInt n
    num <- getOrCreateExprNum key expr
    return (expr, num)

  SSABool b -> do
    let key = KeyBool b
    num <- getOrCreateExprNum key expr
    return (expr, num)

  SSANull -> do
    let key = KeyNull
    num <- getOrCreateExprNum key expr
    return (expr, num)

  SSAStr s -> do
    let key = KeyStr s
    num <- getOrCreateExprNum key expr
    return (expr, num)

  SSAThis -> do
    -- 'this' is unique per method invocation
    num <- freshValueNum
    return (expr, num)

  SSAUse var -> do
    -- Check for replacement
    repl <- gets (Map.lookup (varKey var) . gvnReplacements)
    case repl of
      Just v -> do
        num <- getOrCreateVarNum v
        return (SSAUse (varFromKey v), num)
      Nothing -> do
        num <- getOrCreateVarNum (varKey var)
        return (expr, num)

  SSAUnary op e -> do
    (e', enum) <- valueNumberExpr e
    let key = KeyUnary op enum
    existing <- gets (Map.lookup key . gvnExprToNum)
    case existing of
      Just num -> do
        -- Can we replace with a variable?
        mvar <- gets (Map.lookup num . gvnNumToVar)
        case mvar of
          Just v -> return (SSAUse (varFromKey v), num)
          Nothing -> return (SSAUnary op e', num)
      Nothing -> do
        -- Try to fold constants
        case tryFoldUnary op e' of
          Just folded -> valueNumberExpr folded
          Nothing -> do
            num <- freshValueNum
            recordExpr key num (SSAUnary op e')
            return (SSAUnary op e', num)

  SSABinary op l r -> do
    (l', lnum) <- valueNumberExpr l
    (r', rnum) <- valueNumberExpr r
    -- Normalize commutative operations
    let (lnum', rnum', l'', r'') = if isCommutative op && lnum > rnum
                                    then (rnum, lnum, r', l')
                                    else (lnum, rnum, l', r')
    let key = KeyBinary op lnum' rnum'
    existing <- gets (Map.lookup key . gvnExprToNum)
    case existing of
      Just num -> do
        mvar <- gets (Map.lookup num . gvnNumToVar)
        case mvar of
          Just v -> return (SSAUse (varFromKey v), num)
          Nothing -> return (SSABinary op l'' r'', num)
      Nothing -> do
        -- Try to fold constants
        case tryFoldBinary op l'' r'' of
          Just folded -> valueNumberExpr folded
          Nothing -> do
            num <- freshValueNum
            recordExpr key num (SSABinary op l'' r'')
            return (SSABinary op l'' r'', num)

  SSATernary cond thenE elseE -> do
    (cond', _) <- valueNumberExpr cond
    (thenE', _) <- valueNumberExpr thenE
    (elseE', _) <- valueNumberExpr elseE
    -- Ternaries are not memoized (could depend on control flow)
    num <- freshValueNum
    return (SSATernary cond' thenE' elseE', num)

  SSACall name args -> do
    args' <- mapM (fmap fst . valueNumberExpr) args
    -- Calls are not memoized (side effects)
    num <- freshValueNum
    return (SSACall name args', num)

  SSAInstanceCall target method args -> do
    (target', _) <- valueNumberExpr target
    args' <- mapM (fmap fst . valueNumberExpr) args
    num <- freshValueNum
    return (SSAInstanceCall target' method args', num)

  SSANewObject cn args -> do
    args' <- mapM (fmap fst . valueNumberExpr) args
    num <- freshValueNum
    return (SSANewObject cn args', num)

  SSAFieldAccess target field -> do
    (target', _) <- valueNumberExpr target
    -- Field accesses are not memoized (could be modified)
    num <- freshValueNum
    return (SSAFieldAccess target' field, num)

--------------------------------------------------------------------------------
-- Constant Folding Helpers
--------------------------------------------------------------------------------

-- | Try to fold a unary operation
tryFoldUnary :: UnaryOp -> SSAExpr -> Maybe SSAExpr
tryFoldUnary Neg (SSAInt n) = Just $ SSAInt (-n)
tryFoldUnary Not (SSABool b) = Just $ SSABool (not b)
tryFoldUnary Not (SSAInt n) = Just $ SSABool (n == 0)
tryFoldUnary Not SSANull = Just $ SSABool True
tryFoldUnary _ _ = Nothing

-- | Try to fold a binary operation
tryFoldBinary :: BinaryOp -> SSAExpr -> SSAExpr -> Maybe SSAExpr
tryFoldBinary op (SSAInt l) (SSAInt r) = case op of
  Add -> Just $ SSAInt (l + r)
  Sub -> Just $ SSAInt (l - r)
  Mul -> Just $ SSAInt (l * r)
  Div | r /= 0 -> Just $ SSAInt (l `div` r)
  Mod | r /= 0 -> Just $ SSAInt (l `mod` r)
  Eq -> Just $ SSABool (l == r)
  Ne -> Just $ SSABool (l /= r)
  Lt -> Just $ SSABool (l < r)
  Le -> Just $ SSABool (l <= r)
  Gt -> Just $ SSABool (l > r)
  Ge -> Just $ SSABool (l >= r)
  _ -> Nothing
tryFoldBinary op (SSABool l) (SSABool r) = case op of
  And -> Just $ SSABool (l && r)
  Or -> Just $ SSABool (l || r)
  Eq -> Just $ SSABool (l == r)
  Ne -> Just $ SSABool (l /= r)
  _ -> Nothing
tryFoldBinary _ _ _ = Nothing

-- | Check if an operator is commutative
isCommutative :: BinaryOp -> Bool
isCommutative Add = True
isCommutative Mul = True
isCommutative Eq = True
isCommutative Ne = True
isCommutative And = True
isCommutative Or = True
isCommutative _ = False

--------------------------------------------------------------------------------
-- GVN State Helpers
--------------------------------------------------------------------------------

-- | Get a fresh value number
freshValueNum :: GVN ValueNum
freshValueNum = do
  st <- get
  let num = gvnNextNum st
  put st { gvnNextNum = num + 1 }
  return num

-- | Get or create a value number for a variable
getOrCreateVarNum :: VarKey -> GVN ValueNum
getOrCreateVarNum var = do
  existing <- gets (Map.lookup var . gvnVarToNum)
  case existing of
    Just num -> return num
    Nothing -> do
      num <- freshValueNum
      modify $ \s -> s { gvnVarToNum = Map.insert var num (gvnVarToNum s) }
      return num

-- | Set the value number for a variable
setVarNum :: VarKey -> ValueNum -> GVN ()
setVarNum var num = do
  modify $ \s -> s { gvnVarToNum = Map.insert var num (gvnVarToNum s) }

-- | Get or create a value number for an expression key
getOrCreateExprNum :: ExprKey -> SSAExpr -> GVN ValueNum
getOrCreateExprNum key expr = do
  existing <- gets (Map.lookup key . gvnExprToNum)
  case existing of
    Just num -> return num
    Nothing -> do
      num <- freshValueNum
      recordExpr key num expr
      return num

-- | Record an expression with its value number
recordExpr :: ExprKey -> ValueNum -> SSAExpr -> GVN ()
recordExpr key num expr = do
  modify $ \s -> s
    { gvnExprToNum = Map.insert key num (gvnExprToNum s)
    , gvnNumToExpr = Map.insert num expr (gvnNumToExpr s)
    }

-- | Record a variable replacement
recordReplacement :: VarKey -> VarKey -> GVN ()
recordReplacement from to = do
  modify $ \s -> s
    { gvnReplacements = Map.insert from to (gvnReplacements s)
    , gvnAllReplacements = Map.insert from to (gvnAllReplacements s)
    , gvnElimCount = gvnElimCount s + 1
    }
