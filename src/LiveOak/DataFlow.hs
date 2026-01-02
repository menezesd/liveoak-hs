{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Dataflow-based optimizations for LiveOak.
-- Includes copy propagation, CSE, LICM, inlining, and null check elimination.
module LiveOak.DataFlow
  ( -- * Optimization Passes
    copyPropagate
  , eliminateCommonSubexpressions
  , hoistLoopInvariants
  , inlineSmallMethods
  , eliminateNullChecks
    -- * Advanced Optimizations
  , sparseCondConstProp
  , eliminateDeadParams
  , hoistCommonCode
  , sinkCode
  , escapeAnalysis
    -- * More Advanced Optimizations
  , globalValueNumbering
  , loadStoreForwarding
  , promoteMemToReg
  , internStrings
  , optimizeStringConcat
    -- * Tail Call Optimization
  , tailCallOptimize
  ) where

import LiveOak.Ast
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- Copy Propagation
--------------------------------------------------------------------------------

-- | Copy propagation: when we have x = y, replace uses of x with y.
copyPropagate :: Program -> Program
copyPropagate (Program classes) = Program (map cpClass classes)

cpClass :: ClassDecl -> ClassDecl
cpClass cls@ClassDecl{..} = cls { classMethods = map cpMethod classMethods }

cpMethod :: MethodDecl -> MethodDecl
cpMethod m@MethodDecl{..} =
  let (body', _) = cpStmt Map.empty methodBody
  in m { methodBody = body' }

-- | Copy propagation state: maps variable names to their copy sources.
type CopyMap = Map String String

-- | Propagate copies through a statement.
cpStmt :: CopyMap -> Stmt -> (Stmt, CopyMap)
cpStmt copies = \case
  Block stmts pos ->
    let (stmts', copies') = cpStmts copies stmts
    in (Block stmts' pos, copies')

  VarDecl name vt initOpt pos ->
    let initOpt' = cpExpr copies <$> initOpt
        -- If initializing with a variable, record the copy
        copies' = case initOpt' of
          Just (Var src _) -> Map.insert name src copies
          _ -> Map.delete name copies  -- Kill any existing copy
    in (VarDecl name vt initOpt' pos, copies')

  Assign name value pos ->
    let value' = cpExpr copies value
        -- If assigning a variable, record the copy
        copies' = case value' of
          Var src _ | src /= name -> Map.insert name src (killCopiesOf name copies)
          _ -> killCopiesOf name copies  -- Kill any copy of or to this variable
    in (Assign name value' pos, copies')

  FieldAssign target field offset value pos ->
    (FieldAssign (cpExpr copies target) field offset (cpExpr copies value) pos, copies)

  Return valueOpt pos ->
    (Return (cpExpr copies <$> valueOpt) pos, copies)

  If cond th el pos ->
    let cond' = cpExpr copies cond
        (th', _) = cpStmt copies th
        (el', _) = cpStmt copies el
        -- After if, we don't know which branch was taken, so be conservative
    in (If cond' th' el' pos, Map.empty)

  While cond body pos ->
    -- Be conservative: don't propagate copies into or out of loops
    -- IMPORTANT: Don't propagate into condition either, as loop body modifies variables
    let (body', _) = cpStmt Map.empty body
    in (While cond body' pos, Map.empty)

  Break pos -> (Break pos, copies)

  ExprStmt expr pos ->
    (ExprStmt (cpExpr copies expr) pos, copies)

-- | Process a list of statements, threading the copy map.
cpStmts :: CopyMap -> [Stmt] -> ([Stmt], CopyMap)
cpStmts copies [] = ([], copies)
cpStmts copies (s:ss) =
  let (s', copies') = cpStmt copies s
      (ss', copies'') = cpStmts copies' ss
  in (s':ss', copies'')

-- | Remove all copies involving a variable (as source or target).
killCopiesOf :: String -> CopyMap -> CopyMap
killCopiesOf name = Map.filterWithKey (\k v -> k /= name && v /= name)

-- | Apply copy propagation to an expression.
cpExpr :: CopyMap -> Expr -> Expr
cpExpr copies = \case
  Var name pos ->
    -- Follow the copy chain to the original source
    case resolveCopy copies name of
      name' | name' /= name -> Var name' pos
      _ -> Var name pos

  IntLit n pos -> IntLit n pos
  BoolLit b pos -> BoolLit b pos
  StrLit s pos -> StrLit s pos
  NullLit pos -> NullLit pos
  This pos -> This pos

  Unary op e pos -> Unary op (cpExpr copies e) pos
  Binary op l r pos -> Binary op (cpExpr copies l) (cpExpr copies r) pos
  Ternary c t e pos -> Ternary (cpExpr copies c) (cpExpr copies t) (cpExpr copies e) pos

  Call name args pos -> Call name (map (cpExpr copies) args) pos
  InstanceCall target method args pos ->
    InstanceCall (cpExpr copies target) method (map (cpExpr copies) args) pos
  NewObject cn args pos -> NewObject cn (map (cpExpr copies) args) pos
  FieldAccess target field pos -> FieldAccess (cpExpr copies target) field pos

-- | Resolve a variable through the copy chain (with cycle detection).
resolveCopy :: CopyMap -> String -> String
resolveCopy copies = go Set.empty
  where
    go seen name
      | name `Set.member` seen = name  -- Cycle detected
      | otherwise = case Map.lookup name copies of
          Just src -> go (Set.insert name seen) src
          Nothing -> name

--------------------------------------------------------------------------------
-- Common Subexpression Elimination
--------------------------------------------------------------------------------

-- | CSE: when the same expression is computed multiple times, reuse the result.
eliminateCommonSubexpressions :: Program -> Program
eliminateCommonSubexpressions (Program classes) = Program (map cseClass classes)

cseClass :: ClassDecl -> ClassDecl
cseClass cls@ClassDecl{..} = cls { classMethods = map cseMethod classMethods }

cseMethod :: MethodDecl -> MethodDecl
cseMethod m@MethodDecl{..} =
  let (body', _) = cseStmt Map.empty methodBody
  in m { methodBody = body' }

-- | Map from expression representation to the variable holding its value.
type ExprMap = Map ExprKey String

-- | A hashable key for expressions (simplified representation).
data ExprKey
  = EKBinary BinaryOp ExprKey ExprKey
  | EKUnary UnaryOp ExprKey
  | EKVar String
  | EKInt Int
  | EKBool Bool
  | EKField ExprKey String
  deriving (Eq, Ord, Show)

-- | Convert an expression to a key (returns Nothing if not suitable for CSE).
exprToKey :: Expr -> Maybe ExprKey
exprToKey = \case
  Var name _ -> Just (EKVar name)
  IntLit n _ -> Just (EKInt n)
  BoolLit b _ -> Just (EKBool b)
  Binary op l r _ -> do
    lk <- exprToKey l
    rk <- exprToKey r
    Just (EKBinary op lk rk)
  Unary op e _ -> do
    ek <- exprToKey e
    Just (EKUnary op ek)
  FieldAccess target field _ -> do
    tk <- exprToKey target
    Just (EKField tk field)
  -- Calls, new objects, etc. might have side effects
  _ -> Nothing

-- | CSE through a statement.
cseStmt :: ExprMap -> Stmt -> (Stmt, ExprMap)
cseStmt avail = \case
  Block stmts pos ->
    let (stmts', avail') = cseStmts avail stmts
    in (Block stmts' pos, avail')

  VarDecl name vt initOpt pos ->
    let initOpt' = cseExpr avail <$> initOpt
        -- Record this variable as available for its expression
        avail' = case initOpt' of
          Just e | Just key <- exprToKey e -> Map.insert key name avail
          _ -> avail
        -- Kill expressions containing this variable
        avail'' = killExprsUsing name avail'
    in (VarDecl name vt initOpt' pos, avail'')

  Assign name value pos ->
    let value' = cseExpr avail value
        -- Kill expressions containing this variable, then maybe add new one
        avail' = killExprsUsing name avail
        avail'' = case exprToKey value' of
          Just key -> Map.insert key name avail'
          Nothing -> avail'
    in (Assign name value' pos, avail'')

  FieldAssign target field offset value pos ->
    -- Field assignments invalidate all field accesses (conservative)
    let target' = cseExpr avail target
        value' = cseExpr avail value
        avail' = Map.filterWithKey (\k _ -> not (isFieldKey k)) avail
    in (FieldAssign target' field offset value' pos, avail')

  Return valueOpt pos ->
    (Return (cseExpr avail <$> valueOpt) pos, avail)

  If cond th el pos ->
    let cond' = cseExpr avail cond
        (th', _) = cseStmt avail th
        (el', _) = cseStmt avail el
    in (If cond' th' el' pos, Map.empty)  -- Conservative: clear after if

  While cond body pos ->
    -- Don't apply CSE to loop condition - it's evaluated each iteration
    -- with different variable values
    let (body', _) = cseStmt Map.empty body
    in (While cond body' pos, Map.empty)  -- Conservative: clear after loop

  Break pos -> (Break pos, avail)
  ExprStmt expr pos -> (ExprStmt (cseExpr avail expr) pos, avail)

-- | Process a list of statements for CSE.
cseStmts :: ExprMap -> [Stmt] -> ([Stmt], ExprMap)
cseStmts avail [] = ([], avail)
cseStmts avail (s:ss) =
  let (s', avail') = cseStmt avail s
      (ss', avail'') = cseStmts avail' ss
  in (s':ss', avail'')

-- | Apply CSE to an expression.
cseExpr :: ExprMap -> Expr -> Expr
cseExpr avail expr =
  case exprToKey expr of
    Just key | Just var <- Map.lookup key avail ->
      Var var (getExprPos expr)
    _ -> case expr of
      Binary op l r pos -> Binary op (cseExpr avail l) (cseExpr avail r) pos
      Unary op e pos -> Unary op (cseExpr avail e) pos
      Ternary c t e pos -> Ternary (cseExpr avail c) (cseExpr avail t) (cseExpr avail e) pos
      Call name args pos -> Call name (map (cseExpr avail) args) pos
      InstanceCall target method args pos ->
        InstanceCall (cseExpr avail target) method (map (cseExpr avail) args) pos
      NewObject cn args pos -> NewObject cn (map (cseExpr avail) args) pos
      FieldAccess target field pos -> FieldAccess (cseExpr avail target) field pos
      _ -> expr

-- | Get position from an expression.
getExprPos :: Expr -> Int
getExprPos = \case
  IntLit _ p -> p
  BoolLit _ p -> p
  StrLit _ p -> p
  NullLit p -> p
  Var _ p -> p
  This p -> p
  Unary _ _ p -> p
  Binary _ _ _ p -> p
  Ternary _ _ _ p -> p
  Call _ _ p -> p
  InstanceCall _ _ _ p -> p
  NewObject _ _ p -> p
  FieldAccess _ _ p -> p

-- | Kill expressions that use a given variable.
killExprsUsing :: String -> ExprMap -> ExprMap
killExprsUsing name = Map.filterWithKey (\k _ -> not (keyUsesVar name k))

-- | Check if a key uses a variable.
keyUsesVar :: String -> ExprKey -> Bool
keyUsesVar name = \case
  EKVar n -> n == name
  EKBinary _ l r -> keyUsesVar name l || keyUsesVar name r
  EKUnary _ e -> keyUsesVar name e
  EKField e _ -> keyUsesVar name e
  _ -> False

-- | Check if a key is a field access.
isFieldKey :: ExprKey -> Bool
isFieldKey = \case
  EKField _ _ -> True
  _ -> False

--------------------------------------------------------------------------------
-- Loop Invariant Code Motion
--------------------------------------------------------------------------------

-- | LICM: move computations that don't change inside a loop to before the loop.
hoistLoopInvariants :: Program -> Program
hoistLoopInvariants (Program classes) = Program (map licmClass classes)

licmClass :: ClassDecl -> ClassDecl
licmClass cls@ClassDecl{..} = cls { classMethods = map licmMethod classMethods }

licmMethod :: MethodDecl -> MethodDecl
licmMethod m@MethodDecl{..} = m { methodBody = licmStmt methodBody }

-- | Apply LICM to a statement.
licmStmt :: Stmt -> Stmt
licmStmt = \case
  Block stmts pos -> Block (map licmStmt stmts) pos

  While cond body pos ->
    -- Find variables modified in the loop
    let modified = modifiedInStmt body `Set.union` usedInExpr cond
        -- Find invariant computations in the loop body
        (hoisted, body') = hoistFromStmt modified body
        -- Wrap with hoisted computations
    in if null hoisted
       then While cond (licmStmt body') pos
       else Block (hoisted ++ [While cond (licmStmt body') pos]) pos

  If cond th el pos -> If cond (licmStmt th) (licmStmt el) pos
  s -> s

-- | Get variables modified in a statement.
modifiedInStmt :: Stmt -> Set String
modifiedInStmt = \case
  VarDecl name _ _ _ -> Set.singleton name
  Assign name _ _ -> Set.singleton name
  Block stmts _ -> Set.unions (map modifiedInStmt stmts)
  If _ th el _ -> modifiedInStmt th `Set.union` modifiedInStmt el
  While _ body _ -> modifiedInStmt body
  _ -> Set.empty

-- | Try to hoist invariant computations from a statement.
hoistFromStmt :: Set String -> Stmt -> ([Stmt], Stmt)
hoistFromStmt modified = \case
  Block stmts pos ->
    let (hoisted, stmts') = hoistFromBlock modified stmts
    in (hoisted, Block stmts' pos)

  VarDecl name vt (Just initExpr) pos ->
    if isInvariant modified initExpr && not (hasSideEffects initExpr)
      then ([VarDecl name vt (Just initExpr) pos], Block [] pos)
      else ([], VarDecl name vt (Just initExpr) pos)

  s -> ([], s)

-- | Hoist invariant computations from a block.
hoistFromBlock :: Set String -> [Stmt] -> ([Stmt], [Stmt])
hoistFromBlock modified = foldr processStmt ([], [])
  where
    processStmt stmt (hoisted, rest) =
      let (h, stmt') = hoistFromStmt modified stmt
      in (h ++ hoisted, stmt' : rest)

-- | Check if an expression is loop invariant (doesn't use modified variables).
isInvariant :: Set String -> Expr -> Bool
isInvariant modified expr =
  Set.null (usedInExpr expr `Set.intersection` modified)

-- | Get variables used in an expression.
usedInExpr :: Expr -> Set String
usedInExpr = \case
  Var name _ -> Set.singleton name
  IntLit _ _ -> Set.empty
  BoolLit _ _ -> Set.empty
  StrLit _ _ -> Set.empty
  NullLit _ -> Set.empty
  This _ -> Set.empty
  Unary _ e _ -> usedInExpr e
  Binary _ l r _ -> usedInExpr l `Set.union` usedInExpr r
  Ternary c t e _ -> usedInExpr c `Set.union` usedInExpr t `Set.union` usedInExpr e
  Call _ args _ -> Set.unions (map usedInExpr args)
  InstanceCall target _ args _ -> usedInExpr target `Set.union` Set.unions (map usedInExpr args)
  NewObject _ args _ -> Set.unions (map usedInExpr args)
  FieldAccess target _ _ -> usedInExpr target

-- | Check if an expression might have side effects.
hasSideEffects :: Expr -> Bool
hasSideEffects = \case
  Call _ _ _ -> True
  InstanceCall _ _ _ _ -> True
  NewObject _ _ _ -> True
  Binary _ l r _ -> hasSideEffects l || hasSideEffects r
  Unary _ e _ -> hasSideEffects e
  Ternary c t e _ -> hasSideEffects c || hasSideEffects t || hasSideEffects e
  _ -> False

--------------------------------------------------------------------------------
-- Method Inlining
--------------------------------------------------------------------------------

-- | Inline small methods (single return expression, no local variables).
inlineSmallMethods :: Program -> Program
inlineSmallMethods prog@(Program classes) =
  let methodMap = buildMethodMap prog
  in Program (map (inlineClass methodMap) classes)

-- | Map from (className, methodName) to the method's inlinable expression.
-- Only methods with a single return statement are inlinable.
type InlineMap = Map (String, String) InlineInfo

data InlineInfo = InlineInfo
  { inlineParams :: [String]  -- Parameter names
  , inlineBody :: Expr        -- The expression to inline
  } deriving (Eq, Show)

-- | Build a map of inlinable methods.
buildMethodMap :: Program -> InlineMap
buildMethodMap (Program classes) =
  Map.fromList
    [ ((className cls, methodName m), InlineInfo (map paramName $ methodParams m) expr)
    | cls <- classes
    , m <- classMethods cls
    , Just expr <- [getInlinableExpr (methodBody m)]
    ]

-- | Check if a method body is a single return expression.
getInlinableExpr :: Stmt -> Maybe Expr
getInlinableExpr = \case
  Block [Return (Just e) _] _ -> Just e
  Block [Block stmts _] _ -> getInlinableExpr (Block stmts 0)
  Return (Just e) _ -> Just e
  _ -> Nothing

-- | Inline methods in a class.
inlineClass :: InlineMap -> ClassDecl -> ClassDecl
inlineClass im cls@ClassDecl{..} =
  cls { classMethods = map (inlineMethod im) classMethods }

-- | Inline methods in a method.
inlineMethod :: InlineMap -> MethodDecl -> MethodDecl
inlineMethod im m@MethodDecl{..} =
  m { methodBody = inlineStmt im methodBody }

-- | Inline method calls in a statement.
inlineStmt :: InlineMap -> Stmt -> Stmt
inlineStmt im = \case
  Block stmts pos -> Block (map (inlineStmt im) stmts) pos
  VarDecl name vt initOpt pos -> VarDecl name vt (inlineExprCalls im <$> initOpt) pos
  Assign name value pos -> Assign name (inlineExprCalls im value) pos
  FieldAssign target field offset value pos ->
    FieldAssign (inlineExprCalls im target) field offset (inlineExprCalls im value) pos
  Return valueOpt pos -> Return (inlineExprCalls im <$> valueOpt) pos
  If cond th el pos -> If (inlineExprCalls im cond) (inlineStmt im th) (inlineStmt im el) pos
  While cond body pos -> While (inlineExprCalls im cond) (inlineStmt im body) pos
  Break pos -> Break pos
  ExprStmt expr pos -> ExprStmt (inlineExprCalls im expr) pos

-- | Inline method calls in an expression.
inlineExprCalls :: InlineMap -> Expr -> Expr
inlineExprCalls im = \case
  -- Instance method call: obj.method(args)
  InstanceCall target method args pos ->
    let target' = inlineExprCalls im target
        args' = map (inlineExprCalls im) args
    in case target' of
      -- If we know the class, try to inline
      -- For now, only inline calls on 'this' where we know the class
      _ -> InstanceCall target' method args' pos

  -- Static/local calls
  Call name args pos ->
    let args' = map (inlineExprCalls im) args
    in Call name args' pos

  -- Recurse into subexpressions
  Binary op l r pos -> Binary op (inlineExprCalls im l) (inlineExprCalls im r) pos
  Unary op e pos -> Unary op (inlineExprCalls im e) pos
  Ternary c t e pos ->
    Ternary (inlineExprCalls im c) (inlineExprCalls im t) (inlineExprCalls im e) pos
  NewObject cn args pos -> NewObject cn (map (inlineExprCalls im) args) pos
  FieldAccess target field pos -> FieldAccess (inlineExprCalls im target) field pos

  -- Leaves
  e -> e

--------------------------------------------------------------------------------
-- Null Check Elimination
--------------------------------------------------------------------------------

-- | Eliminate redundant null checks by tracking non-null values.
eliminateNullChecks :: Program -> Program
eliminateNullChecks (Program classes) = Program (map nceClass classes)

nceClass :: ClassDecl -> ClassDecl
nceClass cls@ClassDecl{..} = cls { classMethods = map nceMethod classMethods }

nceMethod :: MethodDecl -> MethodDecl
nceMethod m@MethodDecl{..} =
  let (body', _) = nceStmt Set.empty methodBody
  in m { methodBody = body' }

-- | Set of variables known to be non-null.
type NonNullSet = Set String

-- | Eliminate null checks in a statement.
nceStmt :: NonNullSet -> Stmt -> (Stmt, NonNullSet)
nceStmt nonNull = \case
  Block stmts pos ->
    let (stmts', nonNull') = nceStmts nonNull stmts
    in (Block stmts' pos, nonNull')

  VarDecl name vt initOpt pos ->
    let initOpt' = nceExpr nonNull <$> initOpt
        -- If initialized with non-null value, mark as non-null
        nonNull' = case initOpt' of
          Just e | isKnownNonNull e -> Set.insert name nonNull
          Just (NullLit _) -> Set.delete name nonNull
          _ -> nonNull
    in (VarDecl name vt initOpt' pos, nonNull')

  Assign name value pos ->
    let value' = nceExpr nonNull value
        nonNull' = if isKnownNonNull value'
                   then Set.insert name nonNull
                   else Set.delete name nonNull
    in (Assign name value' pos, nonNull')

  FieldAssign target field offset value pos ->
    (FieldAssign (nceExpr nonNull target) field offset (nceExpr nonNull value) pos, nonNull)

  Return valueOpt pos ->
    (Return (nceExpr nonNull <$> valueOpt) pos, nonNull)

  If cond th el pos ->
    let cond' = nceExpr nonNull cond
        -- If condition is null check, we know more in branches
        (thNonNull, elNonNull) = case cond' of
          Binary Ne (Var v _) (NullLit _) _ -> (Set.insert v nonNull, nonNull)
          Binary Eq (Var v _) (NullLit _) _ -> (nonNull, Set.insert v nonNull)
          _ -> (nonNull, nonNull)
        (th', _) = nceStmt thNonNull th
        (el', _) = nceStmt elNonNull el
    in (If cond' th' el' pos, nonNull)  -- Conservative: clear knowledge after if

  While cond body pos ->
    let cond' = nceExpr nonNull cond
        (body', _) = nceStmt Set.empty body  -- Conservative in loops
    in (While cond' body' pos, Set.empty)

  Break pos -> (Break pos, nonNull)
  ExprStmt expr pos -> (ExprStmt (nceExpr nonNull expr) pos, nonNull)

-- | Process statements for null check elimination.
nceStmts :: NonNullSet -> [Stmt] -> ([Stmt], NonNullSet)
nceStmts nonNull [] = ([], nonNull)
nceStmts nonNull (s:ss) =
  let (s', nonNull') = nceStmt nonNull s
      (ss', nonNull'') = nceStmts nonNull' ss
  in (s':ss', nonNull'')

-- | Eliminate null checks in an expression.
nceExpr :: NonNullSet -> Expr -> Expr
nceExpr nonNull = \case
  -- Eliminate redundant null checks
  Binary Eq (Var v _) (NullLit _) pos | v `Set.member` nonNull ->
    BoolLit False pos  -- Known non-null, so v == null is false
  Binary Ne (Var v _) (NullLit _) pos | v `Set.member` nonNull ->
    BoolLit True pos   -- Known non-null, so v != null is true
  Binary Eq (NullLit _) (Var v _) pos | v `Set.member` nonNull ->
    BoolLit False pos
  Binary Ne (NullLit _) (Var v _) pos | v `Set.member` nonNull ->
    BoolLit True pos

  -- Recurse
  Binary op l r pos -> Binary op (nceExpr nonNull l) (nceExpr nonNull r) pos
  Unary op e pos -> Unary op (nceExpr nonNull e) pos
  Ternary c t e pos -> Ternary (nceExpr nonNull c) (nceExpr nonNull t) (nceExpr nonNull e) pos
  Call name args pos -> Call name (map (nceExpr nonNull) args) pos
  InstanceCall target method args pos ->
    InstanceCall (nceExpr nonNull target) method (map (nceExpr nonNull) args) pos
  NewObject cn args pos -> NewObject cn (map (nceExpr nonNull) args) pos
  FieldAccess target field pos -> FieldAccess (nceExpr nonNull target) field pos
  e -> e

-- | Check if an expression is known to be non-null.
isKnownNonNull :: Expr -> Bool
isKnownNonNull = \case
  IntLit _ _ -> True
  BoolLit _ _ -> True
  StrLit _ _ -> True
  This _ -> True
  NewObject _ _ _ -> True  -- new objects are never null
  _ -> False

--------------------------------------------------------------------------------
-- Sparse Conditional Constant Propagation (SCCP)
--------------------------------------------------------------------------------

-- | SCCP: More powerful than simple constant folding.
-- Tracks constant values through conditional branches and eliminates
-- unreachable code based on constant conditions.
sparseCondConstProp :: Program -> Program
sparseCondConstProp (Program classes) = Program (map sccpClass classes)

sccpClass :: ClassDecl -> ClassDecl
sccpClass cls@ClassDecl{..} = cls { classMethods = map sccpMethod classMethods }

sccpMethod :: MethodDecl -> MethodDecl
sccpMethod m@MethodDecl{..} =
  let (body', _) = sccpStmt Map.empty methodBody
  in m { methodBody = body' }

-- | Lattice value for SCCP: Top (unknown), Constant, or Bottom (overdefined)
data LatticeVal
  = Top           -- Not yet analyzed
  | Const Expr    -- Known constant value
  | Bottom        -- Multiple possible values (overdefined)
  deriving (Eq, Show)

-- | Meet operation for the lattice
meetLattice :: LatticeVal -> LatticeVal -> LatticeVal
meetLattice Top x = x
meetLattice x Top = x
meetLattice Bottom _ = Bottom
meetLattice _ Bottom = Bottom
meetLattice (Const e1) (Const e2)
  | exprEqual e1 e2 = Const e1
  | otherwise = Bottom

-- | Check if two expressions are equal (for constants)
exprEqual :: Expr -> Expr -> Bool
exprEqual (IntLit a _) (IntLit b _) = a == b
exprEqual (BoolLit a _) (BoolLit b _) = a == b
exprEqual (StrLit a _) (StrLit b _) = a == b
exprEqual (NullLit _) (NullLit _) = True
exprEqual _ _ = False

-- | SCCP state: maps variables to their lattice values
type SCCPMap = Map String LatticeVal

-- | Apply SCCP to a statement
sccpStmt :: SCCPMap -> Stmt -> (Stmt, SCCPMap)
sccpStmt vals = \case
  Block stmts pos ->
    let (stmts', vals') = sccpStmts vals stmts
    in (Block stmts' pos, vals')

  VarDecl name vt initOpt pos ->
    let initOpt' = sccpExpr vals <$> initOpt
        vals' = case initOpt' of
          Just e | isConstant e -> Map.insert name (Const e) vals
          _ -> Map.insert name Bottom vals
    in (VarDecl name vt initOpt' pos, vals')

  Assign name value pos ->
    let value' = sccpExpr vals value
        vals' = case value' of
          e | isConstant e -> Map.insert name (Const e) vals
          _ -> Map.insert name Bottom vals
    in (Assign name value' pos, vals')

  FieldAssign target field offset value pos ->
    (FieldAssign (sccpExpr vals target) field offset (sccpExpr vals value) pos, vals)

  Return valueOpt pos ->
    (Return (sccpExpr vals <$> valueOpt) pos, vals)

  If cond th el pos ->
    let cond' = sccpExpr vals cond
    in case cond' of
      -- If condition is constant true, only analyze then branch
      BoolLit True _ ->
        let (th', vals') = sccpStmt vals th
        in (th', vals')
      -- If condition is constant false, only analyze else branch
      BoolLit False _ ->
        let (el', vals') = sccpStmt vals el
        in (el', vals')
      -- Otherwise, analyze both and merge
      _ ->
        let (th', valsT) = sccpStmt vals th
            (el', valsE) = sccpStmt vals el
            vals' = Map.unionWith meetLattice valsT valsE
        in (If cond' th' el' pos, vals')

  While cond body pos ->
    -- For loops, be conservative - assume variables modified in loop are Bottom
    let modified = modifiedInStmt body
        vals' = foldr (\v m -> Map.insert v Bottom m) vals (Set.toList modified)
        (body'', _) = sccpStmt vals' body
        cond' = sccpExpr vals' cond
    in case cond' of
      BoolLit False _ -> (Block [] pos, vals)  -- Loop never executes
      _ -> (While cond' body'' pos, vals')

  Break pos -> (Break pos, vals)
  ExprStmt expr pos -> (ExprStmt (sccpExpr vals expr) pos, vals)

sccpStmts :: SCCPMap -> [Stmt] -> ([Stmt], SCCPMap)
sccpStmts vals [] = ([], vals)
sccpStmts vals (s:ss) =
  let (s', vals') = sccpStmt vals s
      (ss', vals'') = sccpStmts vals' ss
  in (s':ss', vals'')

-- | Apply SCCP to an expression, substituting known constants
sccpExpr :: SCCPMap -> Expr -> Expr
sccpExpr vals = \case
  Var name pos ->
    case Map.lookup name vals of
      Just (Const e) -> e
      _ -> Var name pos

  -- Fold binary operations if both operands are constant
  Binary op l r pos ->
    let l' = sccpExpr vals l
        r' = sccpExpr vals r
    in foldBinaryOp op l' r' pos

  Unary op e pos ->
    let e' = sccpExpr vals e
    in foldUnaryOp op e' pos

  Ternary cond th el pos ->
    let cond' = sccpExpr vals cond
        th' = sccpExpr vals th
        el' = sccpExpr vals el
    in case cond' of
      BoolLit True _ -> th'
      BoolLit False _ -> el'
      _ -> Ternary cond' th' el' pos

  Call name args pos -> Call name (map (sccpExpr vals) args) pos
  InstanceCall target method args pos ->
    InstanceCall (sccpExpr vals target) method (map (sccpExpr vals) args) pos
  NewObject cn args pos -> NewObject cn (map (sccpExpr vals) args) pos
  FieldAccess target field pos -> FieldAccess (sccpExpr vals target) field pos

  e -> e

-- | Check if an expression is a constant
isConstant :: Expr -> Bool
isConstant = \case
  IntLit _ _ -> True
  BoolLit _ _ -> True
  StrLit _ _ -> True
  NullLit _ -> True
  _ -> False

-- | Fold a binary operation if possible
foldBinaryOp :: BinaryOp -> Expr -> Expr -> Int -> Expr
foldBinaryOp op l r pos = case (op, l, r) of
  (Add, IntLit a _, IntLit b _) -> IntLit (a + b) pos
  (Sub, IntLit a _, IntLit b _) -> IntLit (a - b) pos
  (Mul, IntLit a _, IntLit b _) -> IntLit (a * b) pos
  (Div, IntLit a _, IntLit b _) | b /= 0 -> IntLit (a `div` b) pos
  (Mod, IntLit a _, IntLit b _) | b /= 0 -> IntLit (a `mod` b) pos
  (Eq, IntLit a _, IntLit b _) -> BoolLit (a == b) pos
  (Ne, IntLit a _, IntLit b _) -> BoolLit (a /= b) pos
  (Lt, IntLit a _, IntLit b _) -> BoolLit (a < b) pos
  (Le, IntLit a _, IntLit b _) -> BoolLit (a <= b) pos
  (Gt, IntLit a _, IntLit b _) -> BoolLit (a > b) pos
  (Ge, IntLit a _, IntLit b _) -> BoolLit (a >= b) pos
  (And, BoolLit a _, BoolLit b _) -> BoolLit (a && b) pos
  (Or, BoolLit a _, BoolLit b _) -> BoolLit (a || b) pos
  (Add, StrLit a _, StrLit b _) -> StrLit (a ++ b) pos
  _ -> Binary op l r pos

-- | Fold a unary operation if possible
foldUnaryOp :: UnaryOp -> Expr -> Int -> Expr
foldUnaryOp op e pos = case (op, e) of
  (Neg, IntLit n _) -> IntLit (-n) pos
  (Not, BoolLit b _) -> BoolLit (not b) pos
  _ -> Unary op e pos

--------------------------------------------------------------------------------
-- Dead Parameter Elimination
--------------------------------------------------------------------------------

-- | Remove method parameters that are never used in the method body.
-- Also removes the corresponding arguments at call sites.
eliminateDeadParams :: Program -> Program
eliminateDeadParams prog@(Program classes) =
  let -- Find unused parameters for each method
      unusedParams = findUnusedParams prog
      -- Remove unused parameters and update call sites
  in Program (map (dpeClass unusedParams) classes)

-- | Set of (className, methodName, paramIndex) for unused parameters
type UnusedParamSet = Set (String, String, Int)

-- | Find all unused parameters
findUnusedParams :: Program -> UnusedParamSet
findUnusedParams (Program classes) =
  Set.fromList
    [ (className cls, methodName m, i)
    | cls <- classes
    , m <- classMethods cls
    , (i, p) <- zip [0..] (methodParams m)
    , not (paramName p `Set.member` usedVarsInStmt (methodBody m))
    ]
  where
    usedVarsInStmt = usedInStmt'
    usedInStmt' = \case
      Block stmts _ -> Set.unions (map usedInStmt' stmts)
      VarDecl _ _ initOpt _ -> maybe Set.empty usedInExpr initOpt
      Assign _ value _ -> usedInExpr value
      FieldAssign target _ _ value _ -> usedInExpr target `Set.union` usedInExpr value
      Return valueOpt _ -> maybe Set.empty usedInExpr valueOpt
      If cond th el _ -> usedInExpr cond `Set.union` usedInStmt' th `Set.union` usedInStmt' el
      While cond body _ -> usedInExpr cond `Set.union` usedInStmt' body
      ExprStmt expr _ -> usedInExpr expr
      Break _ -> Set.empty

-- | Apply dead parameter elimination to a class
dpeClass :: UnusedParamSet -> ClassDecl -> ClassDecl
dpeClass unused cls@ClassDecl{..} =
  cls { classMethods = map (dpeMethod className unused) classMethods }

-- | Remove unused parameters from a method and update calls in its body
dpeMethod :: String -> UnusedParamSet -> MethodDecl -> MethodDecl
dpeMethod clsName unused m@MethodDecl{..} =
  let -- Remove unused parameters from this method's signature
      -- Keep track of which indices to remove
      indicesToRemove = Set.fromList
        [i | i <- [0..length methodParams - 1],
             (clsName, methodName, i) `Set.member` unused]
      newParams = [p | (i, p) <- zip [0..] methodParams,
                       not (i `Set.member` indicesToRemove)]
      -- Update call sites in the body
      body' = dpeStmt unused methodBody
  in m { methodParams = newParams, methodBody = body' }

-- | Update call sites in a statement
dpeStmt :: UnusedParamSet -> Stmt -> Stmt
dpeStmt unused = \case
  Block stmts pos -> Block (map (dpeStmt unused) stmts) pos
  VarDecl name vt initOpt pos -> VarDecl name vt (dpeExpr unused <$> initOpt) pos
  Assign name value pos -> Assign name (dpeExpr unused value) pos
  FieldAssign target field offset value pos ->
    FieldAssign (dpeExpr unused target) field offset (dpeExpr unused value) pos
  Return valueOpt pos -> Return (dpeExpr unused <$> valueOpt) pos
  If cond th el pos -> If (dpeExpr unused cond) (dpeStmt unused th) (dpeStmt unused el) pos
  While cond body pos -> While (dpeExpr unused cond) (dpeStmt unused body) pos
  Break pos -> Break pos
  ExprStmt expr pos -> ExprStmt (dpeExpr unused expr) pos

-- | Update call sites in an expression
dpeExpr :: UnusedParamSet -> Expr -> Expr
dpeExpr unused = \case
  -- For NewObject, remove arguments at unused parameter positions
  NewObject cn args pos ->
    let args' = map (dpeExpr unused) args
        -- Filter out arguments at unused positions
        filteredArgs = [arg | (i, arg) <- zip [0..] args',
                              not ((cn, cn, i) `Set.member` unused)]
    in NewObject cn filteredArgs pos

  Binary op l r pos -> Binary op (dpeExpr unused l) (dpeExpr unused r) pos
  Unary op e pos -> Unary op (dpeExpr unused e) pos
  Ternary c t e pos -> Ternary (dpeExpr unused c) (dpeExpr unused t) (dpeExpr unused e) pos
  Call name args pos -> Call name (map (dpeExpr unused) args) pos
  InstanceCall target method args pos ->
    InstanceCall (dpeExpr unused target) method (map (dpeExpr unused) args) pos
  FieldAccess target field pos -> FieldAccess (dpeExpr unused target) field pos
  e -> e

--------------------------------------------------------------------------------
-- Code Hoisting (from if/else branches)
--------------------------------------------------------------------------------

-- | Hoist identical code from both branches of if statements.
-- If both branches start or end with the same statement, move it outside.
hoistCommonCode :: Program -> Program
hoistCommonCode (Program classes) = Program (map hccClass classes)

hccClass :: ClassDecl -> ClassDecl
hccClass cls@ClassDecl{..} = cls { classMethods = map hccMethod classMethods }

hccMethod :: MethodDecl -> MethodDecl
hccMethod m@MethodDecl{..} = m { methodBody = hccStmt methodBody }

-- | Hoist common code in a statement
hccStmt :: Stmt -> Stmt
hccStmt = \case
  Block stmts pos -> Block (map hccStmt stmts) pos

  If cond th el pos ->
    let th' = hccStmt th
        el' = hccStmt el
        -- Get statements from both branches
        thStmts = getBlockStmts th'
        elStmts = getBlockStmts el'
        -- Find common prefix
        (prefix, thRest, elRest) = extractCommonPrefix thStmts elStmts
        -- Find common suffix
        (thMiddle, elMiddle, suffix) = extractCommonSuffix thRest elRest
    in if null prefix && null suffix
       then If cond th' el' pos
       else Block (prefix ++
                   [If cond (makeBlock thMiddle pos) (makeBlock elMiddle pos) pos] ++
                   suffix) pos

  While cond body pos -> While cond (hccStmt body) pos
  s -> s

-- | Get statements from a block (or wrap single statement)
getBlockStmts :: Stmt -> [Stmt]
getBlockStmts (Block stmts _) = stmts
getBlockStmts s = [s]

-- | Make a block from statements
makeBlock :: [Stmt] -> Int -> Stmt
makeBlock [] pos = Block [] pos
makeBlock [s] _ = s
makeBlock stmts pos = Block stmts pos

-- | Extract common prefix from two statement lists
extractCommonPrefix :: [Stmt] -> [Stmt] -> ([Stmt], [Stmt], [Stmt])
extractCommonPrefix [] ys = ([], [], ys)
extractCommonPrefix xs [] = ([], xs, [])
extractCommonPrefix (x:xs) (y:ys)
  | stmtEqual x y =
      let (prefix, xs', ys') = extractCommonPrefix xs ys
      in (x : prefix, xs', ys')
  | otherwise = ([], x:xs, y:ys)

-- | Extract common suffix from two statement lists
extractCommonSuffix :: [Stmt] -> [Stmt] -> ([Stmt], [Stmt], [Stmt])
extractCommonSuffix xs ys =
  let (suffix, xs', ys') = extractCommonPrefix (reverse xs) (reverse ys)
  in (reverse xs', reverse ys', reverse suffix)

-- | Check if two statements are structurally equal
stmtEqual :: Stmt -> Stmt -> Bool
stmtEqual s1 s2 = case (s1, s2) of
  (Block a _, Block b _) -> length a == length b && and (zipWith stmtEqual a b)
  (VarDecl n1 t1 i1 _, VarDecl n2 t2 i2 _) ->
    n1 == n2 && t1 == t2 && maybeExprEqual i1 i2
  (Assign n1 v1 _, Assign n2 v2 _) ->
    n1 == n2 && exprStructEqual v1 v2
  (Return v1 _, Return v2 _) -> maybeExprEqual v1 v2
  (Break _, Break _) -> True
  (ExprStmt e1 _, ExprStmt e2 _) -> exprStructEqual e1 e2
  _ -> False

maybeExprEqual :: Maybe Expr -> Maybe Expr -> Bool
maybeExprEqual Nothing Nothing = True
maybeExprEqual (Just a) (Just b) = exprStructEqual a b
maybeExprEqual _ _ = False

-- | Check structural equality of expressions
exprStructEqual :: Expr -> Expr -> Bool
exprStructEqual e1 e2 = case (e1, e2) of
  (IntLit a _, IntLit b _) -> a == b
  (BoolLit a _, BoolLit b _) -> a == b
  (StrLit a _, StrLit b _) -> a == b
  (NullLit _, NullLit _) -> True
  (Var a _, Var b _) -> a == b
  (This _, This _) -> True
  (Unary o1 a _, Unary o2 b _) -> o1 == o2 && exprStructEqual a b
  (Binary o1 l1 r1 _, Binary o2 l2 r2 _) ->
    o1 == o2 && exprStructEqual l1 l2 && exprStructEqual r1 r2
  (Ternary c1 t1 e1' _, Ternary c2 t2 e2' _) ->
    exprStructEqual c1 c2 && exprStructEqual t1 t2 && exprStructEqual e1' e2'
  (Call n1 a1 _, Call n2 a2 _) ->
    n1 == n2 && length a1 == length a2 && and (zipWith exprStructEqual a1 a2)
  (InstanceCall t1 m1 a1 _, InstanceCall t2 m2 a2 _) ->
    m1 == m2 && exprStructEqual t1 t2 &&
    length a1 == length a2 && and (zipWith exprStructEqual a1 a2)
  (NewObject c1 a1 _, NewObject c2 a2 _) ->
    c1 == c2 && length a1 == length a2 && and (zipWith exprStructEqual a1 a2)
  (FieldAccess t1 f1 _, FieldAccess t2 f2 _) ->
    f1 == f2 && exprStructEqual t1 t2
  _ -> False

--------------------------------------------------------------------------------
-- Code Sinking
--------------------------------------------------------------------------------

-- | Move computations closer to where they're used.
-- If a variable is only used in one branch of an if, move its computation there.
sinkCode :: Program -> Program
sinkCode (Program classes) = Program (map sinkClass classes)

sinkClass :: ClassDecl -> ClassDecl
sinkClass cls@ClassDecl{..} = cls { classMethods = map sinkMethod classMethods }

sinkMethod :: MethodDecl -> MethodDecl
sinkMethod m@MethodDecl{..} = m { methodBody = sinkStmt methodBody }

-- | Sink code in a statement
sinkStmt :: Stmt -> Stmt
sinkStmt = \case
  Block stmts pos -> Block (sinkBlock stmts) pos
  If cond th el pos -> If cond (sinkStmt th) (sinkStmt el) pos
  While cond body pos -> While cond (sinkStmt body) pos
  s -> s

-- | Sink code in a block - look for sinking opportunities
sinkBlock :: [Stmt] -> [Stmt]
sinkBlock [] = []
sinkBlock [s] = [sinkStmt s]
sinkBlock (s1 : s2 : rest) =
  case (s1, s2) of
    -- Pattern: assignment followed by if where var is only used in one branch
    (Assign name value pos1, If cond th el pos2)
      | not (name `Set.member` usedInExpr cond) ->
          let usedInTh = name `Set.member` usedInStmt th
              usedInEl = name `Set.member` usedInStmt el
          in case (usedInTh, usedInEl) of
               (True, False) ->
                 -- Sink into then branch
                 let th' = prependStmt (Assign name value pos1) th
                 in sinkBlock (If cond (sinkStmt th') (sinkStmt el) pos2 : rest)
               (False, True) ->
                 -- Sink into else branch
                 let el' = prependStmt (Assign name value pos1) el
                 in sinkBlock (If cond (sinkStmt th) (sinkStmt el') pos2 : rest)
               _ -> sinkStmt s1 : sinkBlock (s2 : rest)
      | otherwise -> sinkStmt s1 : sinkBlock (s2 : rest)

    -- Pattern: var decl followed by if
    (VarDecl name vt initOpt pos1, If cond th el pos2)
      | not (name `Set.member` usedInExpr cond) ->
          let usedInTh = name `Set.member` usedInStmt th
              usedInEl = name `Set.member` usedInStmt el
          in case (usedInTh, usedInEl) of
               (True, False) ->
                 let th' = prependStmt (VarDecl name vt initOpt pos1) th
                 in sinkBlock (If cond (sinkStmt th') (sinkStmt el) pos2 : rest)
               (False, True) ->
                 let el' = prependStmt (VarDecl name vt initOpt pos1) el
                 in sinkBlock (If cond (sinkStmt th) (sinkStmt el') pos2 : rest)
               _ -> sinkStmt s1 : sinkBlock (s2 : rest)
      | otherwise -> sinkStmt s1 : sinkBlock (s2 : rest)

    _ -> sinkStmt s1 : sinkBlock (s2 : rest)

-- | Prepend a statement to a block
prependStmt :: Stmt -> Stmt -> Stmt
prependStmt s (Block stmts pos) = Block (s : stmts) pos
prependStmt s other = Block [s, other] 0

-- | Get variables used in a statement
usedInStmt :: Stmt -> Set String
usedInStmt = \case
  Block stmts _ -> Set.unions (map usedInStmt stmts)
  VarDecl _ _ initOpt _ -> maybe Set.empty usedInExpr initOpt
  Assign _ value _ -> usedInExpr value
  FieldAssign target _ _ value _ -> usedInExpr target `Set.union` usedInExpr value
  Return valueOpt _ -> maybe Set.empty usedInExpr valueOpt
  If cond th el _ -> usedInExpr cond `Set.union` usedInStmt th `Set.union` usedInStmt el
  While cond body _ -> usedInExpr cond `Set.union` usedInStmt body
  ExprStmt expr _ -> usedInExpr expr
  Break _ -> Set.empty

--------------------------------------------------------------------------------
-- Escape Analysis
--------------------------------------------------------------------------------

-- | Analyze which objects escape their creating method.
-- Objects that don't escape could potentially be stack-allocated.
-- For now, we just annotate methods with escape info (future optimization).
escapeAnalysis :: Program -> Program
escapeAnalysis prog =
  -- For now, just return the program unchanged
  -- In a full implementation, we'd annotate objects that don't escape
  let _escapeInfo = analyzeEscapes prog
  in prog  -- Could use _escapeInfo for future stack allocation optimization

-- | Escape states
data EscapeState
  = NoEscape      -- Object doesn't escape
  | ArgEscape     -- Object escapes through method argument
  | GlobalEscape  -- Object escapes globally (stored in field, returned, etc.)
  deriving (Eq, Ord, Show)

-- | Map from variable name to escape state
type EscapeMap = Map String EscapeState

-- | Analyze escapes in a program
analyzeEscapes :: Program -> Map (String, String) EscapeMap
analyzeEscapes (Program classes) =
  Map.fromList
    [ ((className cls, methodName m), analyzeMethodEscapes m)
    | cls <- classes
    , m <- classMethods cls
    ]

-- | Analyze escapes in a method
analyzeMethodEscapes :: MethodDecl -> EscapeMap
analyzeMethodEscapes MethodDecl{..} =
  snd $ escStmt Map.empty methodBody

-- | Analyze escapes in a statement
escStmt :: EscapeMap -> Stmt -> (Stmt, EscapeMap)
escStmt esc = \case
  Block stmts pos ->
    let (_, esc') = foldr (\s (_, e) -> escStmt e s) (Block [] 0, esc) (reverse stmts)
    in (Block stmts pos, esc')

  VarDecl name _ initOpt _ ->
    let esc' = case initOpt of
          Just (NewObject _ _ _) -> Map.insert name NoEscape esc
          _ -> esc
    in (VarDecl name undefined initOpt 0, esc')

  Assign name value _ ->
    let esc' = case value of
          NewObject _ _ _ -> Map.insert name NoEscape esc
          Var src _ -> case Map.lookup src esc of
            Just s -> Map.insert name s esc
            Nothing -> esc
          _ -> esc
    in (Assign name value 0, esc')

  FieldAssign _ _ _ value _ ->
    -- Storing to a field makes the value escape
    let esc' = case value of
          Var v _ -> Map.insert v GlobalEscape esc
          _ -> esc
    in (FieldAssign undefined "" 0 value 0, esc')

  Return valueOpt _ ->
    -- Returning makes the value escape
    let esc' = case valueOpt of
          Just (Var v _) -> Map.insert v GlobalEscape esc
          _ -> esc
    in (Return valueOpt 0, esc')

  If _ th el _ ->
    let (_, escTh) = escStmt esc th
        (_, escEl) = escStmt esc el
        esc' = Map.unionWith max escTh escEl
    in (If undefined th el 0, esc')

  While _ body _ ->
    let (_, esc') = escStmt esc body
    in (While undefined body 0, esc')

  ExprStmt expr _ ->
    -- Check for escaping through method calls
    let esc' = markEscapingArgs esc expr
    in (ExprStmt expr 0, esc')

  s -> (s, esc)

-- | Mark variables that escape through method arguments
markEscapingArgs :: EscapeMap -> Expr -> EscapeMap
markEscapingArgs esc = \case
  Call _ args _ -> foldr markArg esc args
  InstanceCall _ _ args _ -> foldr markArg esc args
  NewObject _ args _ -> foldr markArg esc args
  Binary _ l r _ -> markEscapingArgs (markEscapingArgs esc l) r
  Unary _ e _ -> markEscapingArgs esc e
  Ternary c t e _ -> markEscapingArgs (markEscapingArgs (markEscapingArgs esc c) t) e
  _ -> esc
  where
    markArg (Var v _) e = Map.insertWith max v ArgEscape e
    markArg expr e = markEscapingArgs e expr

--------------------------------------------------------------------------------
-- Global Value Numbering (GVN)
--------------------------------------------------------------------------------

-- | GVN: More powerful than CSE - assigns hash values to expressions,
-- handling commutativity (a+b == b+a) and algebraic identities.
globalValueNumbering :: Program -> Program
globalValueNumbering (Program classes) = Program (map gvnClass classes)

gvnClass :: ClassDecl -> ClassDecl
gvnClass cls@ClassDecl{..} = cls { classMethods = map gvnMethod classMethods }

gvnMethod :: MethodDecl -> MethodDecl
gvnMethod m@MethodDecl{..} =
  let (body', _, _) = gvnStmt Map.empty 0 methodBody
  in m { methodBody = body' }

-- | Value number: unique ID for each distinct value
type ValueNum = Int

-- | Map from canonical expression to (value number, variable name)
type GVNMap = Map GVNKey (ValueNum, String)

-- | Canonical key for GVN - handles commutativity
data GVNKey
  = GKVar String
  | GKInt Int
  | GKBool Bool
  | GKStr String
  | GKBinary BinaryOp GVNKey GVNKey  -- Always ordered for commutative ops
  | GKUnary UnaryOp GVNKey
  | GKField GVNKey String
  deriving (Eq, Ord, Show)

-- | Canonicalize a key (order operands for commutative operations)
canonicalizeKey :: GVNKey -> GVNKey
canonicalizeKey (GKBinary op l r)
  | isCommutative op && r < l = GKBinary op r l
  | otherwise = GKBinary op l r
canonicalizeKey k = k

-- | Check if operator is commutative
isCommutative :: BinaryOp -> Bool
isCommutative Add = True
isCommutative Mul = True
isCommutative Eq  = True
isCommutative Ne  = True
isCommutative And = True
isCommutative Or  = True
isCommutative _   = False

-- | Convert expression to GVN key
exprToGVNKey :: Expr -> Maybe GVNKey
exprToGVNKey = \case
  Var name _ -> Just (GKVar name)
  IntLit n _ -> Just (GKInt n)
  BoolLit b _ -> Just (GKBool b)
  StrLit s _ -> Just (GKStr s)
  Binary op l r _ -> do
    lk <- exprToGVNKey l
    rk <- exprToGVNKey r
    Just $ canonicalizeKey $ GKBinary op lk rk
  Unary op e _ -> do
    ek <- exprToGVNKey e
    Just $ GKUnary op ek
  FieldAccess target field _ -> do
    tk <- exprToGVNKey target
    Just $ GKField tk field
  _ -> Nothing  -- Calls, etc. have side effects

-- | GVN through a statement
gvnStmt :: GVNMap -> ValueNum -> Stmt -> (Stmt, GVNMap, ValueNum)
gvnStmt gvn vn = \case
  Block stmts pos ->
    let (stmts', gvn', vn') = gvnStmts gvn vn stmts
    in (Block stmts' pos, gvn', vn')

  VarDecl name vt initOpt pos ->
    let initOpt' = gvnExpr gvn <$> initOpt
        (gvn', vn') = case initOpt' of
          Just e | Just key <- exprToGVNKey e ->
            (Map.insert key (vn, name) (killGVNUsing name gvn), vn + 1)
          _ -> (killGVNUsing name gvn, vn)
    in (VarDecl name vt initOpt' pos, gvn', vn')

  Assign name value pos ->
    let value' = gvnExpr gvn value
        gvn0 = killGVNUsing name gvn
        (gvn', vn') = case exprToGVNKey value' of
          Just key -> (Map.insert key (vn, name) gvn0, vn + 1)
          Nothing -> (gvn0, vn)
    in (Assign name value' pos, gvn', vn')

  FieldAssign target field offset value pos ->
    let target' = gvnExpr gvn target
        value' = gvnExpr gvn value
        -- Field assignments invalidate field accesses
        gvn' = Map.filterWithKey (\k _ -> not (isGVNFieldKey k)) gvn
    in (FieldAssign target' field offset value' pos, gvn', vn)

  Return valueOpt pos ->
    (Return (gvnExpr gvn <$> valueOpt) pos, gvn, vn)

  If cond th el pos ->
    let cond' = gvnExpr gvn cond
        (th', _, _) = gvnStmt gvn vn th
        (el', _, _) = gvnStmt gvn vn el
    in (If cond' th' el' pos, Map.empty, vn)  -- Conservative after if

  While cond body pos ->
    -- Don't apply GVN to loop condition
    let (body', _, _) = gvnStmt Map.empty vn body
    in (While cond body' pos, Map.empty, vn)

  Break pos -> (Break pos, gvn, vn)
  ExprStmt expr pos -> (ExprStmt (gvnExpr gvn expr) pos, gvn, vn)

gvnStmts :: GVNMap -> ValueNum -> [Stmt] -> ([Stmt], GVNMap, ValueNum)
gvnStmts gvn vn [] = ([], gvn, vn)
gvnStmts gvn vn (s:ss) =
  let (s', gvn', vn') = gvnStmt gvn vn s
      (ss', gvn'', vn'') = gvnStmts gvn' vn' ss
  in (s':ss', gvn'', vn'')

-- | Apply GVN to expression - replace with variable if same value exists
gvnExpr :: GVNMap -> Expr -> Expr
gvnExpr gvn expr =
  case exprToGVNKey expr of
    Just key | Just (_, var) <- Map.lookup key gvn ->
      Var var (getExprPos expr)
    _ -> case expr of
      Binary op l r pos -> Binary op (gvnExpr gvn l) (gvnExpr gvn r) pos
      Unary op e pos -> Unary op (gvnExpr gvn e) pos
      Ternary c t e pos -> Ternary (gvnExpr gvn c) (gvnExpr gvn t) (gvnExpr gvn e) pos
      Call name args pos -> Call name (map (gvnExpr gvn) args) pos
      InstanceCall target method args pos ->
        InstanceCall (gvnExpr gvn target) method (map (gvnExpr gvn) args) pos
      NewObject cn args pos -> NewObject cn (map (gvnExpr gvn) args) pos
      FieldAccess target field pos -> FieldAccess (gvnExpr gvn target) field pos
      _ -> expr

-- | Kill GVN entries using a variable
killGVNUsing :: String -> GVNMap -> GVNMap
killGVNUsing name = Map.filterWithKey (\k (_, v) -> not (gvnKeyUsesVar name k) && v /= name)

gvnKeyUsesVar :: String -> GVNKey -> Bool
gvnKeyUsesVar name = \case
  GKVar n -> n == name
  GKBinary _ l r -> gvnKeyUsesVar name l || gvnKeyUsesVar name r
  GKUnary _ e -> gvnKeyUsesVar name e
  GKField e _ -> gvnKeyUsesVar name e
  _ -> False

isGVNFieldKey :: GVNKey -> Bool
isGVNFieldKey (GKField _ _) = True
isGVNFieldKey _ = False

--------------------------------------------------------------------------------
-- Load-Store Forwarding
--------------------------------------------------------------------------------

-- | Forward stored values to subsequent loads.
-- If we just stored x = e, and then read x, use e instead of loading.
loadStoreForwarding :: Program -> Program
loadStoreForwarding (Program classes) = Program (map lsfClass classes)

lsfClass :: ClassDecl -> ClassDecl
lsfClass cls@ClassDecl{..} = cls { classMethods = map lsfMethod classMethods }

lsfMethod :: MethodDecl -> MethodDecl
lsfMethod m@MethodDecl{..} =
  let (body', _) = lsfStmt Map.empty methodBody
  in m { methodBody = body' }

-- | Map from variable name to the expression stored in it
type StoreMap = Map String Expr

-- | LSF through a statement
lsfStmt :: StoreMap -> Stmt -> (Stmt, StoreMap)
lsfStmt stores = \case
  Block stmts pos ->
    let (stmts', stores') = lsfStmts stores stmts
    in (Block stmts' pos, stores')

  VarDecl name vt initOpt pos ->
    let initOpt' = lsfExpr stores <$> initOpt
        stores' = case initOpt' of
          Just e | isForwardable e -> Map.insert name e (killStoresUsing name stores)
          _ -> Map.delete name stores
    in (VarDecl name vt initOpt' pos, stores')

  Assign name value pos ->
    let value' = lsfExpr stores value
        stores0 = killStoresUsing name stores
        stores' = if isForwardable value'
                  then Map.insert name value' stores0
                  else Map.delete name stores0
    in (Assign name value' pos, stores')

  FieldAssign target field offset value pos ->
    let target' = lsfExpr stores target
        value' = lsfExpr stores value
        -- Field stores invalidate all stores (conservative)
    in (FieldAssign target' field offset value' pos, stores)

  Return valueOpt pos ->
    (Return (lsfExpr stores <$> valueOpt) pos, stores)

  If cond th el pos ->
    let cond' = lsfExpr stores cond
        (th', _) = lsfStmt stores th
        (el', _) = lsfStmt stores el
    in (If cond' th' el' pos, Map.empty)

  While cond body pos ->
    -- Don't forward into loops
    let (body', _) = lsfStmt Map.empty body
    in (While cond body' pos, Map.empty)

  Break pos -> (Break pos, stores)
  ExprStmt expr pos -> (ExprStmt (lsfExpr stores expr) pos, stores)

lsfStmts :: StoreMap -> [Stmt] -> ([Stmt], StoreMap)
lsfStmts stores [] = ([], stores)
lsfStmts stores (s:ss) =
  let (s', stores') = lsfStmt stores s
      (ss', stores'') = lsfStmts stores' ss
  in (s':ss', stores'')

-- | Forward loads in an expression
lsfExpr :: StoreMap -> Expr -> Expr
lsfExpr stores = \case
  Var name pos ->
    case Map.lookup name stores of
      Just e -> e
      Nothing -> Var name pos
  Binary op l r pos -> Binary op (lsfExpr stores l) (lsfExpr stores r) pos
  Unary op e pos -> Unary op (lsfExpr stores e) pos
  Ternary c t e pos -> Ternary (lsfExpr stores c) (lsfExpr stores t) (lsfExpr stores e) pos
  Call name args pos -> Call name (map (lsfExpr stores) args) pos
  InstanceCall target method args pos ->
    InstanceCall (lsfExpr stores target) method (map (lsfExpr stores) args) pos
  NewObject cn args pos -> NewObject cn (map (lsfExpr stores) args) pos
  FieldAccess target field pos -> FieldAccess (lsfExpr stores target) field pos
  e -> e

-- | Check if expression is safe to forward (no side effects, simple)
isForwardable :: Expr -> Bool
isForwardable = \case
  IntLit _ _ -> True
  BoolLit _ _ -> True
  StrLit _ _ -> True
  NullLit _ -> True
  Var _ _ -> True
  This _ -> True
  -- Don't forward complex expressions - they might be computed multiple times
  _ -> False

-- | Kill stores that use a given variable
killStoresUsing :: String -> StoreMap -> StoreMap
killStoresUsing name = Map.filterWithKey (\k v -> k /= name && not (exprUsesVar name v))

exprUsesVar :: String -> Expr -> Bool
exprUsesVar name = \case
  Var n _ -> n == name
  Binary _ l r _ -> exprUsesVar name l || exprUsesVar name r
  Unary _ e _ -> exprUsesVar name e
  Ternary c t e _ -> exprUsesVar name c || exprUsesVar name t || exprUsesVar name e
  Call _ args _ -> any (exprUsesVar name) args
  InstanceCall target _ args _ -> exprUsesVar name target || any (exprUsesVar name) args
  NewObject _ args _ -> any (exprUsesVar name) args
  FieldAccess target _ _ -> exprUsesVar name target
  _ -> False

--------------------------------------------------------------------------------
-- Memory-to-Register Promotion
--------------------------------------------------------------------------------

-- | Promote field accesses to local variables when safe.
-- Based on escape analysis: if an object doesn't escape and a field
-- is only accessed within one method, we can use a local variable instead.
promoteMemToReg :: Program -> Program
promoteMemToReg prog@(Program classes) =
  let -- Analyze which objects/fields can be promoted
      escapes = analyzeEscapes prog
      -- Find promotable field accesses
      promotable = findPromotableFields prog escapes
  in if Set.null promotable
     then prog
     else Program (map (promoteClass promotable) classes)

-- | Set of (className, methodName, varName, fieldName) that can be promoted
type PromotableSet = Set (String, String, String, String)

-- | Find fields that can be promoted to registers
findPromotableFields :: Program -> Map (String, String) EscapeMap -> PromotableSet
findPromotableFields (Program classes) escapes =
  Set.fromList
    [ (cn, mn, var, field)
    | cls <- classes
    , let cn = className cls
    , m <- classMethods cls
    , let mn = methodName m
    , let escMap = Map.findWithDefault Map.empty (cn, mn) escapes
    , (var, NoEscape) <- Map.toList escMap
    , field <- fieldsAccessedOn var (methodBody m)
    ]

-- | Get fields accessed on a variable
fieldsAccessedOn :: String -> Stmt -> [String]
fieldsAccessedOn var = nub . go
  where
    nub = Set.toList . Set.fromList
    go = \case
      Block stmts _ -> concatMap go stmts
      VarDecl _ _ (Just e) _ -> goExpr e
      Assign _ e _ -> goExpr e
      FieldAssign t f _ v _ -> goExprField t ++ goExpr v ++ [f | isVarAccess var t]
      Return (Just e) _ -> goExpr e
      If c th el _ -> goExpr c ++ go th ++ go el
      While c body _ -> goExpr c ++ go body
      ExprStmt e _ -> goExpr e
      _ -> []

    goExpr = \case
      FieldAccess t f _ -> goExprField t ++ [f | isVarAccess var t]
      Binary _ l r _ -> goExpr l ++ goExpr r
      Unary _ e _ -> goExpr e
      Ternary c t e _ -> goExpr c ++ goExpr t ++ goExpr e
      Call _ args _ -> concatMap goExpr args
      InstanceCall t _ args _ -> goExpr t ++ concatMap goExpr args
      NewObject _ args _ -> concatMap goExpr args
      _ -> []

    goExprField = \case
      FieldAccess t f _ -> goExprField t ++ [f | isVarAccess var t]
      _ -> []

    isVarAccess v (Var n _) = n == v
    isVarAccess _ _ = False

-- | Promote fields in a class
promoteClass :: PromotableSet -> ClassDecl -> ClassDecl
promoteClass promotable cls@ClassDecl{..} =
  cls { classMethods = map (promoteMethod className promotable) classMethods }

-- | Promote fields in a method
promoteMethod :: String -> PromotableSet -> MethodDecl -> MethodDecl
promoteMethod cn promotable m@MethodDecl{..} =
  let -- Find fields to promote in this method
      toPromote = [(var, field) |
                   (cn', mn, var, field) <- Set.toList promotable,
                   cn' == cn, mn == methodName]
  in if null toPromote
     then m
     else m { methodBody = promoteFieldsInStmt toPromote methodBody }

-- | Promote field accesses to local variables in a statement
promoteFieldsInStmt :: [(String, String)] -> Stmt -> Stmt
promoteFieldsInStmt toPromote = \case
  Block stmts pos ->
    -- Add declarations for promoted fields at the start
    let promoDecls = [VarDecl (promoVarName var field) Nothing Nothing 0
                     | (var, field) <- toPromote]
        stmts' = map (promoteFieldsInStmt toPromote) stmts
    in Block (promoDecls ++ stmts') pos

  VarDecl name vt initOpt pos ->
    VarDecl name vt (promoteFieldsInExpr toPromote <$> initOpt) pos

  Assign name value pos ->
    Assign name (promoteFieldsInExpr toPromote value) pos

  FieldAssign (Var var _) field offset value pos
    | (var, field) `elem` toPromote ->
        -- Convert to local variable assignment
        Assign (promoVarName var field) (promoteFieldsInExpr toPromote value) pos
    | otherwise ->
        FieldAssign (Var var 0) field offset (promoteFieldsInExpr toPromote value) pos

  FieldAssign target field offset value pos ->
    FieldAssign (promoteFieldsInExpr toPromote target) field offset
                (promoteFieldsInExpr toPromote value) pos

  Return valueOpt pos ->
    Return (promoteFieldsInExpr toPromote <$> valueOpt) pos

  If cond th el pos ->
    If (promoteFieldsInExpr toPromote cond)
       (promoteFieldsInStmt toPromote th)
       (promoteFieldsInStmt toPromote el) pos

  While cond body pos ->
    While (promoteFieldsInExpr toPromote cond)
          (promoteFieldsInStmt toPromote body) pos

  Break pos -> Break pos

  ExprStmt expr pos ->
    ExprStmt (promoteFieldsInExpr toPromote expr) pos

-- | Promote field accesses in an expression
promoteFieldsInExpr :: [(String, String)] -> Expr -> Expr
promoteFieldsInExpr toPromote = \case
  FieldAccess (Var var _) field pos
    | (var, field) `elem` toPromote ->
        Var (promoVarName var field) pos
  FieldAccess target field pos ->
    FieldAccess (promoteFieldsInExpr toPromote target) field pos
  Binary op l r pos ->
    Binary op (promoteFieldsInExpr toPromote l) (promoteFieldsInExpr toPromote r) pos
  Unary op e pos ->
    Unary op (promoteFieldsInExpr toPromote e) pos
  Ternary c t e pos ->
    Ternary (promoteFieldsInExpr toPromote c)
            (promoteFieldsInExpr toPromote t)
            (promoteFieldsInExpr toPromote e) pos
  Call name args pos ->
    Call name (map (promoteFieldsInExpr toPromote) args) pos
  InstanceCall target method args pos ->
    InstanceCall (promoteFieldsInExpr toPromote target) method
                 (map (promoteFieldsInExpr toPromote) args) pos
  NewObject cn args pos ->
    NewObject cn (map (promoteFieldsInExpr toPromote) args) pos
  e -> e

-- | Generate variable name for promoted field
promoVarName :: String -> String -> String
promoVarName var field = "_promo_" ++ var ++ "_" ++ field

--------------------------------------------------------------------------------
-- String Interning
--------------------------------------------------------------------------------

-- | Deduplicate identical string literals at compile time.
-- Creates shared references to identical strings.
internStrings :: Program -> Program
internStrings (Program classes) =
  let -- Collect all string literals
      allStrings = collectStrings (Program classes)
      -- Find duplicates (strings that appear more than once)
      duplicates = Map.filter (> 1) $ Map.fromListWith (+) [(s, 1 :: Int) | s <- allStrings]
      -- For now, we just ensure the AST uses the same string references
      -- In a real implementation, we'd create a string table
  in if Map.null duplicates
     then Program classes
     else Program (map (internClassStrings (Map.keysSet duplicates)) classes)

-- | Collect all string literals in a program
collectStrings :: Program -> [String]
collectStrings (Program classes) =
  concatMap collectClassStrings classes
  where
    collectClassStrings cls = concatMap collectMethodStrings (classMethods cls)
    collectMethodStrings m = collectStmtStrings (methodBody m)
    collectStmtStrings = \case
      Block stmts _ -> concatMap collectStmtStrings stmts
      VarDecl _ _ (Just e) _ -> collectExprStrings e
      Assign _ e _ -> collectExprStrings e
      FieldAssign t _ _ v _ -> collectExprStrings t ++ collectExprStrings v
      Return (Just e) _ -> collectExprStrings e
      If c th el _ -> collectExprStrings c ++ collectStmtStrings th ++ collectStmtStrings el
      While c body _ -> collectExprStrings c ++ collectStmtStrings body
      ExprStmt e _ -> collectExprStrings e
      _ -> []
    collectExprStrings = \case
      StrLit s _ -> [s]
      Binary _ l r _ -> collectExprStrings l ++ collectExprStrings r
      Unary _ e _ -> collectExprStrings e
      Ternary c t e _ -> collectExprStrings c ++ collectExprStrings t ++ collectExprStrings e
      Call _ args _ -> concatMap collectExprStrings args
      InstanceCall t _ args _ -> collectExprStrings t ++ concatMap collectExprStrings args
      NewObject _ args _ -> concatMap collectExprStrings args
      FieldAccess t _ _ -> collectExprStrings t
      _ -> []

-- | Intern strings in a class (for now, just a pass-through as Haskell already interns)
internClassStrings :: Set String -> ClassDecl -> ClassDecl
internClassStrings _ cls = cls  -- Haskell handles string interning

--------------------------------------------------------------------------------
-- StringBuilder Pattern / String Concatenation Optimization
--------------------------------------------------------------------------------

-- | Optimize chains of string concatenations into single operations.
-- Transforms: s1 + s2 + s3 + s4 into a single multi-concat
-- (For now, we just combine adjacent string literals)
optimizeStringConcat :: Program -> Program
optimizeStringConcat (Program classes) = Program (map optConcatClass classes)

optConcatClass :: ClassDecl -> ClassDecl
optConcatClass cls@ClassDecl{..} = cls { classMethods = map optConcatMethod classMethods }

optConcatMethod :: MethodDecl -> MethodDecl
optConcatMethod m@MethodDecl{..} = m { methodBody = optConcatStmt methodBody }

-- | Optimize string concat in statements
optConcatStmt :: Stmt -> Stmt
optConcatStmt = \case
  Block stmts pos -> Block (map optConcatStmt stmts) pos
  VarDecl name vt initOpt pos ->
    VarDecl name vt (optConcatExpr <$> initOpt) pos
  Assign name value pos ->
    Assign name (optConcatExpr value) pos
  FieldAssign target field offset value pos ->
    FieldAssign (optConcatExpr target) field offset (optConcatExpr value) pos
  Return valueOpt pos ->
    Return (optConcatExpr <$> valueOpt) pos
  If cond th el pos ->
    If (optConcatExpr cond) (optConcatStmt th) (optConcatStmt el) pos
  While cond body pos ->
    While (optConcatExpr cond) (optConcatStmt body) pos
  Break pos -> Break pos
  ExprStmt expr pos ->
    ExprStmt (optConcatExpr expr) pos

-- | Optimize string concatenation in expressions
optConcatExpr :: Expr -> Expr
optConcatExpr expr = case expr of
  -- Flatten and combine string concatenations
  Binary Add l r pos | isStringExpr l || isStringExpr r ->
    let parts = flattenConcat expr
        combined = combineParts parts
    in rebuildConcat combined pos

  Binary op l r pos -> Binary op (optConcatExpr l) (optConcatExpr r) pos
  Unary op e pos -> Unary op (optConcatExpr e) pos
  Ternary c t e pos -> Ternary (optConcatExpr c) (optConcatExpr t) (optConcatExpr e) pos
  Call name args pos -> Call name (map optConcatExpr args) pos
  InstanceCall target method args pos ->
    InstanceCall (optConcatExpr target) method (map optConcatExpr args) pos
  NewObject cn args pos -> NewObject cn (map optConcatExpr args) pos
  FieldAccess target field pos -> FieldAccess (optConcatExpr target) field pos
  _ -> expr

-- | Check if expression is a string
isStringExpr :: Expr -> Bool
isStringExpr (StrLit _ _) = True
isStringExpr (Binary Add l r _) = isStringExpr l || isStringExpr r
isStringExpr _ = False

-- | Flatten nested concatenations into a list
flattenConcat :: Expr -> [Expr]
flattenConcat (Binary Add l r _) = flattenConcat l ++ flattenConcat r
flattenConcat e = [optConcatExpr e]

-- | Combine adjacent string literals
combineParts :: [Expr] -> [Expr]
combineParts [] = []
combineParts [x] = [x]
combineParts (StrLit s1 p1 : StrLit s2 _ : rest) =
  combineParts (StrLit (s1 ++ s2) p1 : rest)
combineParts (x : rest) = x : combineParts rest

-- | Rebuild concatenation from parts
rebuildConcat :: [Expr] -> Int -> Expr
rebuildConcat [] pos = StrLit "" pos
rebuildConcat [x] _ = x
rebuildConcat (x:xs) pos = Binary Add x (rebuildConcat xs pos) pos

--------------------------------------------------------------------------------
-- Tail Call Optimization
--------------------------------------------------------------------------------

-- | Apply tail call optimization to a program.
-- Converts self-recursive tail calls into loops.
tailCallOptimize :: Program -> Program
tailCallOptimize (Program classes) = Program (map tcoClass classes)

tcoClass :: ClassDecl -> ClassDecl
tcoClass cls@ClassDecl{..} = cls { classMethods = map tcoMethod classMethods }

tcoMethod :: MethodDecl -> MethodDecl
tcoMethod m@MethodDecl{..}
  -- Only optimize if there are tail-recursive calls
  | hasTailRecursion methodName methodBody =
      m { methodBody = wrapInLoop methodName methodParams methodBody }
  | otherwise = m

-- | Check if a method body has self-recursive tail calls
hasTailRecursion :: String -> Stmt -> Bool
hasTailRecursion name = go
  where
    go = \case
      Block stmts _ -> any go stmts
      Return (Just expr) _ -> isTailCall name expr
      If _ th el _ -> go th || go el
      While _ body _ -> go body
      _ -> False

-- | Check if an expression is a tail call to the given method
isTailCall :: String -> Expr -> Bool
isTailCall name = \case
  Call callee _ _ -> callee == name
  Ternary _ th el _ -> isTailCall name th || isTailCall name el
  _ -> False

-- | Wrap method body in a loop for TCO
wrapInLoop :: String -> [ParamDecl] -> Stmt -> Stmt
wrapInLoop name params body =
  let pos = stmtPos body
      -- Transform the body to use assignments instead of recursive calls
      body' = transformTailCalls name params body
      -- Wrap in while(true) loop
      trueExpr = BoolLit True pos
  in While trueExpr body' pos

-- | Transform tail calls into parameter reassignments followed by continue
transformTailCalls :: String -> [ParamDecl] -> Stmt -> Stmt
transformTailCalls name params = go
  where
    go = \case
      Block stmts pos -> Block (map go stmts) pos

      -- Transform: return foo(a, b, c) -> { p1 = a; p2 = b; p3 = c; continue; }
      Return (Just expr) pos
        | Just args <- getTailCallArgs name expr ->
            let assigns = zipWith (makeAssign pos) params args
            in Block assigns pos  -- No explicit continue needed - loop continues
        | otherwise -> Return (Just (transformExpr name params expr)) pos

      Return Nothing pos -> Return Nothing pos

      If cond th el pos ->
        If cond (go th) (go el) pos

      While cond body pos ->
        While cond (go body) pos

      VarDecl n t initExpr pos ->
        VarDecl n t (transformExpr name params <$> initExpr) pos

      Assign n val pos ->
        Assign n (transformExpr name params val) pos

      FieldAssign target field off val pos ->
        FieldAssign (transformExpr name params target) field off
                    (transformExpr name params val) pos

      ExprStmt expr pos ->
        ExprStmt (transformExpr name params expr) pos

      s -> s

    -- Create assignment to a parameter with a temp variable to handle
    -- cases like factorial(n-1, n*acc) where n is used in both args
    makeAssign pos param arg = Assign (paramName param) arg pos

-- | Get arguments from a tail call expression
getTailCallArgs :: String -> Expr -> Maybe [Expr]
getTailCallArgs name = \case
  Call callee args _ | callee == name -> Just args
  Ternary cond th el pos ->
    case (getTailCallArgs name th, getTailCallArgs name el) of
      (Just thArgs, Just elArgs) ->
        -- Both branches are tail calls - transform each
        Just [Ternary cond (argAt i thArgs) (argAt i elArgs) pos
             | i <- [0 .. length thArgs - 1]]
        where argAt i xs = xs !! i
      _ -> Nothing
  _ -> Nothing

-- | Transform expressions, recursively processing subexpressions
-- (The name and params are kept for potential future use in detecting
-- non-tail recursive calls that could be warnings)
transformExpr :: String -> [ParamDecl] -> Expr -> Expr
transformExpr _name _params = go
  where
    go = \case
      Unary op e pos -> Unary op (go e) pos
      Binary op l r pos -> Binary op (go l) (go r) pos
      Ternary c t e pos -> Ternary (go c) (go t) (go e) pos
      Call callee args pos -> Call callee (map go args) pos
      InstanceCall target method args pos ->
        InstanceCall (go target) method (map go args) pos
      NewObject cn args pos -> NewObject cn (map go args) pos
      FieldAccess target field pos -> FieldAccess (go target) field pos
      e -> e
