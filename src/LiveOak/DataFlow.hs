{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Dataflow-based optimizations for LiveOak.
-- Includes CSE, GVN, LICM, inlining, and null check elimination.
--
-- Note: Copy propagation and constant propagation are handled by
-- SSA.structuredSSAOpt which provides SSA-style value tracking.
module LiveOak.DataFlow
  ( -- * Core Dataflow Optimizations
    eliminateCommonSubexpressions
  , globalValueNumbering
  , hoistLoopInvariants
  , loadStoreForwarding
  , eliminateDeadStores
    -- * Method Optimizations
  , inlineSmallMethods
  , eliminateDeadParams
  , tailCallOptimize
  , aggressiveInline
    -- * Code Motion
  , hoistCommonCode
  , sinkCode
    -- * Memory Optimizations
  , escapeAnalysis
  , promoteMemToReg
    -- * Null Check Elimination
  , eliminateNullChecks
    -- * String Optimizations
  , internStrings
  , optimizeStringConcat
    -- * Loop Optimizations
  , unrollLoops
  , fuseLoops
    -- * Range Analysis
  , eliminateImpossibleBranches
  ) where

import LiveOak.Ast
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

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
-- Dead Store Elimination
--------------------------------------------------------------------------------

-- | Eliminate dead stores: assignments to variables that are overwritten
-- before being read. This is safe at the AST level because we can remove
-- the entire assignment including the value computation.
--
-- A store is dead if:
-- 1. The variable is assigned again before any read
-- 2. The assigned expression has no side effects
-- 3. No control flow (if/while/break/return) occurs between stores
eliminateDeadStores :: Program -> Program
eliminateDeadStores (Program classes) = Program (map dseClass classes)

dseClass :: ClassDecl -> ClassDecl
dseClass cls@ClassDecl{..} = cls { classMethods = map dseMethod classMethods }

dseMethod :: MethodDecl -> MethodDecl
dseMethod m@MethodDecl{..} = m { methodBody = dseStmt methodBody }

-- | Eliminate dead stores in a statement
dseStmt :: Stmt -> Stmt
dseStmt = \case
  Block stmts pos -> Block (dseBlock stmts) pos
  If cond th el pos -> If cond (dseStmt th) (dseStmt el) pos
  While cond body pos -> While cond (dseStmt body) pos
  s -> s

-- | Eliminate dead stores in a block
-- Process statements and remove dead assignments
dseBlock :: [Stmt] -> [Stmt]
dseBlock = go
  where
    go [] = []
    go [s] = [dseStmt s]
    go (s1 : s2 : rest) = case (s1, s2) of
      -- Pattern: x = e1; x = e2  (consecutive assignments to same var)
      (Assign name1 value1 _, Assign name2 _ _)
        | name1 == name2, not (hasSideEffects value1) ->
            go (s2 : rest)  -- Remove dead store s1

      -- Pattern: x = e1; ... ; x = e2 with no reads of x between
      (Assign name value _, _)
        | not (hasSideEffects value)
        , isDeadBeforeRead name (s2 : rest) ->
            go (s2 : rest)  -- Remove dead store s1

      -- Pattern: var x = e1; x = e2 (init followed by overwrite)
      (VarDecl name _ (Just value) _, Assign name2 _ _)
        | name == name2, not (hasSideEffects value) ->
            -- Keep the declaration but without init, then continue
            VarDecl name Nothing Nothing 0 : go (s2 : rest)

      -- Pattern: var x = e1; ... ; x = e2 with no reads of x between
      (VarDecl name _ (Just value) pos, _)
        | not (hasSideEffects value)
        , isDeadBeforeRead name (s2 : rest) ->
            VarDecl name Nothing Nothing pos : go (s2 : rest)

      -- No dead store pattern matched
      _ -> dseStmt s1 : go (s2 : rest)

-- | Check if a variable is dead (overwritten before read) in the given statements
-- Returns True if we find an assignment to the variable before any read
-- Conservative: returns False on control flow (if/while/return/break)
isDeadBeforeRead :: String -> [Stmt] -> Bool
isDeadBeforeRead _ [] = False
isDeadBeforeRead name (s:rest) = case s of
  -- Found assignment to name - it's dead
  Assign n _ _ | n == name -> True
  VarDecl n _ (Just _) _ | n == name -> True

  -- Check if statement reads the variable - if so, not dead
  Assign _ value _ | exprUsesVar name value -> False
  VarDecl _ _ (Just value) _ | exprUsesVar name value -> False
  FieldAssign target _ _ value _ | exprUsesVar name target || exprUsesVar name value -> False
  Return (Just value) _ | exprUsesVar name value -> False
  ExprStmt expr _ | exprUsesVar name expr -> False

  -- Control flow - conservatively say not dead
  If {} -> False
  While {} -> False
  Return _ _ -> False
  Break _ -> False

  -- Other statements without reads - continue checking
  _ -> isDeadBeforeRead name rest

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

--------------------------------------------------------------------------------
-- Loop Unrolling
--------------------------------------------------------------------------------

-- | Unroll small loops with known iteration counts.
-- Patterns detected:
--   while (i < N) { body; i = i + 1; }  where N is a small constant
--   int i = 0; while (i < N) { body; i = i + 1; }
unrollLoops :: Program -> Program
unrollLoops (Program classes) = Program (map unrollClass classes)

unrollClass :: ClassDecl -> ClassDecl
unrollClass cls@ClassDecl{..} = cls { classMethods = map unrollMethod classMethods }

unrollMethod :: MethodDecl -> MethodDecl
unrollMethod m@MethodDecl{..} = m { methodBody = unrollStmt methodBody }

-- | Maximum number of iterations to unroll
maxUnrollCount :: Int
maxUnrollCount = 8

-- | Maximum body size (in AST nodes) to unroll
maxUnrollBodySize :: Int
maxUnrollBodySize = 20

-- | Unroll loops in a statement
unrollStmt :: Stmt -> Stmt
unrollStmt = \case
  Block stmts pos -> Block (unrollBlock stmts) pos
  If cond th el pos -> If cond (unrollStmt th) (unrollStmt el) pos
  While cond body pos -> tryUnroll cond body pos
  s -> s

-- | Try to unroll a block, looking for init-then-loop patterns
unrollBlock :: [Stmt] -> [Stmt]
unrollBlock [] = []
unrollBlock [s] = [unrollStmt s]
unrollBlock (s1 : s2 : rest) = case (s1, s2) of
  -- Pattern: int i = 0; while (i < N) { body; i = i + 1; }
  (VarDecl name _ (Just (IntLit initVal _)) _, While cond body pos)
    | Just (loopVar, limit) <- getLoopBound cond
    , loopVar == name
    , initVal == 0
    , Just increment <- getLoopIncrement name body
    , increment == 1
    , limit > 0 && limit <= maxUnrollCount
    , stmtSize body <= maxUnrollBodySize
    , not (hasBreak body) ->
        let -- Remove the increment from body
            bodyWithoutIncr = removeIncrement name body
            -- Generate unrolled iterations
            unrolled = [substituteVar name i bodyWithoutIncr | i <- [0..limit-1]]
        in Block unrolled pos : unrollBlock rest

  _ -> unrollStmt s1 : unrollBlock (s2 : rest)

-- | Try to unroll a while loop
-- NOTE: We can only unroll loops where we know the initial value from context.
-- The unrollBlock function handles init-then-loop patterns where init value is known.
-- For standalone while loops without known init value, we just recurse into body.
tryUnroll :: Expr -> Stmt -> Int -> Stmt
tryUnroll cond body pos =
  -- We don't know the initial value of the loop variable here, so we can't
  -- safely unroll. The unrollBlock function handles cases where init is known.
  While cond (unrollStmt body) pos

-- | Extract loop bound from condition: i < N returns (i, N)
getLoopBound :: Expr -> Maybe (String, Int)
getLoopBound = \case
  Binary Lt (Var name _) (IntLit n _) _ -> Just (name, n)
  Binary Le (Var name _) (IntLit n _) _ -> Just (name, n + 1)
  Binary Gt (IntLit n _) (Var name _) _ -> Just (name, n)
  Binary Ge (IntLit n _) (Var name _) _ -> Just (name, n + 1)
  _ -> Nothing

-- | Get loop increment: look for i = i + 1 or i = i - 1
getLoopIncrement :: String -> Stmt -> Maybe Int
getLoopIncrement name = \case
  Block stmts _ ->
    case filter isIncrement stmts of
      [s] -> getLoopIncrement name s
      _ -> Nothing
  Assign n (Binary Add (Var v _) (IntLit delta _) _) _
    | n == name && v == name -> Just delta
  Assign n (Binary Sub (Var v _) (IntLit delta _) _) _
    | n == name && v == name -> Just (-delta)
  _ -> Nothing
  where
    isIncrement (Assign n _ _) = n == name
    isIncrement _ = False

-- | Remove increment statement from loop body
removeIncrement :: String -> Stmt -> Stmt
removeIncrement name = \case
  Block stmts pos -> Block (filter (not . isIncrement) stmts) pos
  s -> s
  where
    isIncrement (Assign n (Binary Add (Var v _) (IntLit _ _) _) _) = n == name && v == name
    isIncrement (Assign n (Binary Sub (Var v _) (IntLit _ _) _) _) = n == name && v == name
    isIncrement _ = False

-- | Substitute a variable with a constant in a statement
substituteVar :: String -> Int -> Stmt -> Stmt
substituteVar name val = \case
  Block stmts pos -> Block (map (substituteVar name val) stmts) pos
  VarDecl n vt initOpt pos -> VarDecl n vt (substExpr name val <$> initOpt) pos
  Assign n value pos -> Assign n (substExpr name val value) pos
  FieldAssign target field offset value pos ->
    FieldAssign (substExpr name val target) field offset (substExpr name val value) pos
  Return valueOpt pos -> Return (substExpr name val <$> valueOpt) pos
  If cond th el pos ->
    If (substExpr name val cond) (substituteVar name val th) (substituteVar name val el) pos
  While cond body pos -> While (substExpr name val cond) (substituteVar name val body) pos
  Break pos -> Break pos
  ExprStmt expr pos -> ExprStmt (substExpr name val expr) pos

-- | Substitute variable with constant in expression
substExpr :: String -> Int -> Expr -> Expr
substExpr name val = \case
  Var n pos | n == name -> IntLit val pos
  Var n pos -> Var n pos
  IntLit n pos -> IntLit n pos
  BoolLit b pos -> BoolLit b pos
  StrLit s pos -> StrLit s pos
  NullLit pos -> NullLit pos
  This pos -> This pos
  Unary op e pos -> Unary op (substExpr name val e) pos
  Binary op l r pos -> Binary op (substExpr name val l) (substExpr name val r) pos
  Ternary c t e pos -> Ternary (substExpr name val c) (substExpr name val t) (substExpr name val e) pos
  Call n args pos -> Call n (map (substExpr name val) args) pos
  InstanceCall target method args pos ->
    InstanceCall (substExpr name val target) method (map (substExpr name val) args) pos
  NewObject cn args pos -> NewObject cn (map (substExpr name val) args) pos
  FieldAccess target field pos -> FieldAccess (substExpr name val target) field pos

-- | Check if statement contains break
hasBreak :: Stmt -> Bool
hasBreak = \case
  Break _ -> True
  Block stmts _ -> any hasBreak stmts
  If _ th el _ -> hasBreak th || hasBreak el
  While _ body _ -> hasBreak body
  _ -> False

-- | Estimate statement size for unrolling decisions
stmtSize :: Stmt -> Int
stmtSize = \case
  Block stmts _ -> sum (map stmtSize stmts)
  VarDecl _ _ (Just e) _ -> 1 + exprSize e
  VarDecl _ _ Nothing _ -> 1
  Assign _ e _ -> 1 + exprSize e
  FieldAssign t _ _ v _ -> 2 + exprSize t + exprSize v
  Return (Just e) _ -> 1 + exprSize e
  Return Nothing _ -> 1
  If c th el _ -> 1 + exprSize c + stmtSize th + stmtSize el
  While c body _ -> 1 + exprSize c + stmtSize body
  Break _ -> 1
  ExprStmt e _ -> exprSize e

-- | Estimate expression size
exprSize :: Expr -> Int
exprSize = \case
  IntLit _ _ -> 1
  BoolLit _ _ -> 1
  StrLit _ _ -> 1
  NullLit _ -> 1
  Var _ _ -> 1
  This _ -> 1
  Unary _ e _ -> 1 + exprSize e
  Binary _ l r _ -> 1 + exprSize l + exprSize r
  Ternary c t e _ -> 1 + exprSize c + exprSize t + exprSize e
  Call _ args _ -> 1 + sum (map exprSize args)
  InstanceCall target _ args _ -> 1 + exprSize target + sum (map exprSize args)
  NewObject _ args _ -> 1 + sum (map exprSize args)
  FieldAccess target _ _ -> 1 + exprSize target

--------------------------------------------------------------------------------
-- Value Range Analysis
--------------------------------------------------------------------------------

-- | Value range: [lower, upper] bounds for integers
data Range = Range
  { rangeLower :: Maybe Int  -- Nothing = negative infinity
  , rangeUpper :: Maybe Int  -- Nothing = positive infinity
  } deriving (Eq, Show)

-- | Full range (unknown)
fullRange :: Range
fullRange = Range Nothing Nothing

-- | Exact value range
exactRange :: Int -> Range
exactRange n = Range (Just n) (Just n)

-- | Map from variable to its known range
type RangeMap = Map String Range

-- | Eliminate branches that are impossible based on value range analysis.
-- Tracks integer ranges through assignments and conditions.
eliminateImpossibleBranches :: Program -> Program
eliminateImpossibleBranches (Program classes) = Program (map rangeClass classes)

rangeClass :: ClassDecl -> ClassDecl
rangeClass cls@ClassDecl{..} = cls { classMethods = map rangeMethod classMethods }

rangeMethod :: MethodDecl -> MethodDecl
rangeMethod m@MethodDecl{..} =
  let (body', _) = rangeStmt Map.empty methodBody
  in m { methodBody = body' }

-- | Analyze ranges and eliminate impossible branches
rangeStmt :: RangeMap -> Stmt -> (Stmt, RangeMap)
rangeStmt ranges = \case
  Block stmts pos ->
    let (stmts', ranges') = rangeStmts ranges stmts
    in (Block stmts' pos, ranges')

  VarDecl name vt initOpt pos ->
    let initOpt' = rangeExpr ranges <$> initOpt
        -- Track the range of the initialized value
        ranges' = case initOpt' of
          Just (IntLit n _) -> Map.insert name (exactRange n) ranges
          Just (Binary Add (Var v _) (IntLit n _) _) ->
            case Map.lookup v ranges of
              Just (Range (Just lo) (Just hi)) ->
                Map.insert name (Range (Just (lo + n)) (Just (hi + n))) ranges
              _ -> Map.delete name ranges
          _ -> Map.delete name ranges
    in (VarDecl name vt initOpt' pos, ranges')

  Assign name value pos ->
    let value' = rangeExpr ranges value
        ranges0 = Map.delete name ranges
        ranges' = case value' of
          IntLit n _ -> Map.insert name (exactRange n) ranges0
          Binary Add (Var v _) (IntLit n _) _ | v == name ->
            case Map.lookup name ranges of
              Just (Range (Just lo) (Just hi)) ->
                Map.insert name (Range (Just (lo + n)) (Just (hi + n))) ranges0
              Just (Range (Just lo) Nothing) | n >= 0 ->
                Map.insert name (Range (Just (lo + n)) Nothing) ranges0
              _ -> ranges0
          Var v _ -> case Map.lookup v ranges of
            Just r -> Map.insert name r ranges0
            Nothing -> ranges0
          _ -> ranges0
    in (Assign name value' pos, ranges')

  FieldAssign target field offset value pos ->
    (FieldAssign (rangeExpr ranges target) field offset (rangeExpr ranges value) pos, ranges)

  Return valueOpt pos ->
    (Return (rangeExpr ranges <$> valueOpt) pos, ranges)

  If cond th el pos ->
    let cond' = rangeExpr ranges cond
    in case evalCondition ranges cond' of
      Just True ->
        let (th', _) = rangeStmt ranges th
        in (th', ranges)  -- Condition always true
      Just False ->
        let (el', _) = rangeStmt ranges el
        in (el', ranges) -- Condition always false
      Nothing ->
        -- Refine ranges for each branch based on condition
        let (thRanges, elRanges) = refineRanges ranges cond'
            (th', _) = rangeStmt thRanges th
            (el', _) = rangeStmt elRanges el
        in (If cond' th' el' pos, ranges)  -- Conservative: don't extend ranges after if

  While cond body pos ->
    let cond' = rangeExpr ranges cond
        -- IMPORTANT: Variables modified in the loop may have any value after
        -- the first iteration, so we must clear their ranges before analyzing
        -- the loop body. Otherwise we might incorrectly eliminate branches.
        modifiedVars = findModifiedVars body
        bodyRanges = foldr Map.delete ranges modifiedVars
        -- Refine ranges based on condition (only applies to unmodified vars)
        (bodyRanges', _) = refineRanges bodyRanges cond'
        (body', _) = rangeStmt bodyRanges' body
    in (While cond' body' pos, Map.empty)  -- Conservative after loop

  Break pos -> (Break pos, ranges)
  ExprStmt expr pos -> (ExprStmt (rangeExpr ranges expr) pos, ranges)

-- | Process statements with range tracking
rangeStmts :: RangeMap -> [Stmt] -> ([Stmt], RangeMap)
rangeStmts ranges [] = ([], ranges)
rangeStmts ranges (s:ss) =
  let (s', ranges') = rangeStmt ranges s
      (ss', ranges'') = rangeStmts ranges' ss
  in (s':ss', ranges'')

-- | Find all variables that are assigned (modified) in a statement
findModifiedVars :: Stmt -> [String]
findModifiedVars = \case
  Block stmts _ -> concatMap findModifiedVars stmts
  VarDecl name _ _ _ -> [name]  -- Declaration counts as modification
  Assign name _ _ -> [name]
  FieldAssign _ _ _ _ _ -> []  -- Field assigns don't modify local vars
  Return _ _ -> []
  If _ th el _ -> findModifiedVars th ++ findModifiedVars el
  While _ body _ -> findModifiedVars body
  Break _ -> []
  ExprStmt _ _ -> []

-- | Apply range info to expression
-- Note: We intentionally don't replace variables with constants here
-- to avoid infinite loops with constant propagation. The SSA pass handles that.
rangeExpr :: RangeMap -> Expr -> Expr
rangeExpr _ranges = id  -- Just pass through - range info is only used for branch elimination

-- | Evaluate a condition to a constant if possible
evalCondition :: RangeMap -> Expr -> Maybe Bool
evalCondition ranges = \case
  BoolLit b _ -> Just b

  -- x < n: if x's upper bound < n, always true; if x's lower bound >= n, always false
  Binary Lt (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range _ (Just hi)) | hi < n -> Just True   -- upper < n means always true
      Just (Range (Just lo) _) | lo >= n -> Just False -- lower >= n means always false
      _ -> Nothing

  -- x <= n: if upper <= n, always true; if lower > n, always false
  Binary Le (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range _ (Just hi)) | hi <= n -> Just True
      Just (Range (Just lo) _) | lo > n -> Just False
      _ -> Nothing

  -- x > n: if lower > n, always true; if upper <= n, always false
  Binary Gt (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range (Just lo) _) | lo > n -> Just True
      Just (Range _ (Just hi)) | hi <= n -> Just False
      _ -> Nothing

  -- x >= n: if lower >= n, always true; if upper < n, always false
  Binary Ge (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range (Just lo) _) | lo >= n -> Just True
      Just (Range _ (Just hi)) | hi < n -> Just False
      _ -> Nothing

  -- x == n: if range is exactly n, always true; if n is outside range, always false
  Binary Eq (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range (Just lo) (Just hi)) | lo == hi && lo == n -> Just True
      Just (Range (Just lo) _) | lo > n -> Just False
      Just (Range _ (Just hi)) | hi < n -> Just False
      _ -> Nothing

  -- x != n: if n is outside range, always true; if range is exactly n, always false
  Binary Ne (Var name _) (IntLit n _) _ ->
    case Map.lookup name ranges of
      Just (Range (Just lo) (Just hi)) | lo == hi && lo == n -> Just False
      Just (Range (Just lo) _) | lo > n -> Just True
      Just (Range _ (Just hi)) | hi < n -> Just True
      _ -> Nothing

  _ -> Nothing

-- | Refine ranges based on condition being true (for then branch) or false (for else branch)
refineRanges :: RangeMap -> Expr -> (RangeMap, RangeMap)
refineRanges ranges = \case
  -- x < n: then branch has x in [lo, n-1], else branch has x in [n, hi]
  Binary Lt (Var name _) (IntLit n _) _ ->
    let current = Map.findWithDefault fullRange name ranges
        thenRange = current { rangeUpper = Just (min (maybe (n-1) id (rangeUpper current)) (n-1)) }
        elseRange = current { rangeLower = Just (max (maybe n id (rangeLower current)) n) }
    in (Map.insert name thenRange ranges, Map.insert name elseRange ranges)

  -- x <= n: then has [lo, n], else has [n+1, hi]
  Binary Le (Var name _) (IntLit n _) _ ->
    let current = Map.findWithDefault fullRange name ranges
        thenRange = current { rangeUpper = Just (min (maybe n id (rangeUpper current)) n) }
        elseRange = current { rangeLower = Just (max (maybe (n+1) id (rangeLower current)) (n+1)) }
    in (Map.insert name thenRange ranges, Map.insert name elseRange ranges)

  -- x > n: then has [n+1, hi], else has [lo, n]
  Binary Gt (Var name _) (IntLit n _) _ ->
    let current = Map.findWithDefault fullRange name ranges
        thenRange = current { rangeLower = Just (max (maybe (n+1) id (rangeLower current)) (n+1)) }
        elseRange = current { rangeUpper = Just (min (maybe n id (rangeUpper current)) n) }
    in (Map.insert name thenRange ranges, Map.insert name elseRange ranges)

  -- x >= n: then has [n, hi], else has [lo, n-1]
  Binary Ge (Var name _) (IntLit n _) _ ->
    let current = Map.findWithDefault fullRange name ranges
        thenRange = current { rangeLower = Just (max (maybe n id (rangeLower current)) n) }
        elseRange = current { rangeUpper = Just (min (maybe (n-1) id (rangeUpper current)) (n-1)) }
    in (Map.insert name thenRange ranges, Map.insert name elseRange ranges)

  -- x == n: then has [n, n], else keeps current range (can't narrow much)
  Binary Eq (Var name _) (IntLit n _) _ ->
    (Map.insert name (exactRange n) ranges, ranges)

  -- x != n: then keeps range, else has [n, n]
  Binary Ne (Var name _) (IntLit n _) _ ->
    (ranges, Map.insert name (exactRange n) ranges)

  -- For other conditions, don't refine
  _ -> (ranges, ranges)

--------------------------------------------------------------------------------
-- Aggressive Inlining
--------------------------------------------------------------------------------

-- | More aggressive inlining based on size and call frequency heuristics.
aggressiveInline :: Program -> Program
aggressiveInline prog@(Program classes) =
  let -- Find inlinable methods (small enough)
      inlineCandidates = findInlineCandidates prog
      -- Inline them
  in if Map.null inlineCandidates
     then prog
     else Program (map (aggressiveInlineClass inlineCandidates) classes)

-- | Max size for inlining (AST nodes)
maxInlineSize :: Int
maxInlineSize = 30

-- | Find methods suitable for inlining
findInlineCandidates :: Program -> Map (String, String) MethodDecl
findInlineCandidates (Program classes) =
  Map.fromList
    [((className cls, methodName m), m)
    | cls <- classes
    , m <- classMethods cls
    , stmtSize (methodBody m) <= maxInlineSize
    , not (isRecursive (className cls) m)
    ]
  where
    isRecursive clsName m = callsSelf clsName (methodName m) (methodBody m)

    callsSelf clsName mName = \case
      Block stmts _ -> any (callsSelf clsName mName) stmts
      VarDecl _ _ (Just e) _ -> exprCallsSelf clsName mName e
      Assign _ e _ -> exprCallsSelf clsName mName e
      FieldAssign _ _ _ e _ -> exprCallsSelf clsName mName e
      Return (Just e) _ -> exprCallsSelf clsName mName e
      If c th el _ -> exprCallsSelf clsName mName c || callsSelf clsName mName th || callsSelf clsName mName el
      While c body _ -> exprCallsSelf clsName mName c || callsSelf clsName mName body
      ExprStmt e _ -> exprCallsSelf clsName mName e
      _ -> False

    exprCallsSelf clsName mName = \case
      Call name _ _ -> name == mName || name == clsName ++ "_" ++ mName
      InstanceCall (This _) method _ _ -> method == mName
      Binary _ l r _ -> exprCallsSelf clsName mName l || exprCallsSelf clsName mName r
      Unary _ e _ -> exprCallsSelf clsName mName e
      Ternary c t e _ -> any (exprCallsSelf clsName mName) [c, t, e]
      InstanceCall target _ args _ -> any (exprCallsSelf clsName mName) (target : args)
      NewObject _ args _ -> any (exprCallsSelf clsName mName) args
      FieldAccess t _ _ -> exprCallsSelf clsName mName t
      _ -> False

aggressiveInlineClass :: Map (String, String) MethodDecl -> ClassDecl -> ClassDecl
aggressiveInlineClass candidates cls@ClassDecl{..} =
  cls { classMethods = map (aggressiveInlineMethod candidates className) classMethods }

aggressiveInlineMethod :: Map (String, String) MethodDecl -> String -> MethodDecl -> MethodDecl
aggressiveInlineMethod candidates clsName m@MethodDecl{..} =
  m { methodBody = inlineInStmt candidates clsName methodBody }

inlineInStmt :: Map (String, String) MethodDecl -> String -> Stmt -> Stmt
inlineInStmt candidates clsName = \case
  Block stmts pos -> Block (map (inlineInStmt candidates clsName) stmts) pos
  VarDecl name vt initOpt pos -> VarDecl name vt (inlineInExpr candidates clsName <$> initOpt) pos
  Assign name value pos -> Assign name (inlineInExpr candidates clsName value) pos
  FieldAssign target field offset value pos ->
    FieldAssign (inlineInExpr candidates clsName target) field offset (inlineInExpr candidates clsName value) pos
  Return valueOpt pos -> Return (inlineInExpr candidates clsName <$> valueOpt) pos
  If cond th el pos ->
    If (inlineInExpr candidates clsName cond) (inlineInStmt candidates clsName th) (inlineInStmt candidates clsName el) pos
  While cond body pos -> While (inlineInExpr candidates clsName cond) (inlineInStmt candidates clsName body) pos
  Break pos -> Break pos
  ExprStmt expr pos -> ExprStmt (inlineInExpr candidates clsName expr) pos

inlineInExpr :: Map (String, String) MethodDecl -> String -> Expr -> Expr
inlineInExpr candidates clsName = \case
  -- Try to inline local calls
  Call name args pos ->
    let args' = map (inlineInExpr candidates clsName) args
    in case Map.lookup (clsName, name) candidates of
      Just m | Just result <- tryInline m args' -> result
      _ -> Call name args' pos

  Binary op l r pos -> Binary op (inlineInExpr candidates clsName l) (inlineInExpr candidates clsName r) pos
  Unary op e pos -> Unary op (inlineInExpr candidates clsName e) pos
  Ternary c t e pos ->
    Ternary (inlineInExpr candidates clsName c) (inlineInExpr candidates clsName t) (inlineInExpr candidates clsName e) pos
  InstanceCall target method args pos ->
    InstanceCall (inlineInExpr candidates clsName target) method (map (inlineInExpr candidates clsName) args) pos
  NewObject cn args pos -> NewObject cn (map (inlineInExpr candidates clsName) args) pos
  FieldAccess target field pos -> FieldAccess (inlineInExpr candidates clsName target) field pos
  e -> e

-- | Try to inline a method call
tryInline :: MethodDecl -> [Expr] -> Maybe Expr
tryInline m args =
  case getReturnExpr (methodBody m) of
    Just retExpr ->
      let paramNames = map paramName (methodParams m)
          subst = Map.fromList (zip paramNames args)
      in Just (substituteExprs subst retExpr)
    Nothing -> Nothing

getReturnExpr :: Stmt -> Maybe Expr
getReturnExpr = \case
  Return (Just e) _ -> Just e
  Block [s] _ -> getReturnExpr s
  Block stmts _ -> getReturnExpr (last stmts)
  _ -> Nothing

substituteExprs :: Map String Expr -> Expr -> Expr
substituteExprs subst = \case
  Var name pos -> Map.findWithDefault (Var name pos) name subst
  Binary op l r pos -> Binary op (substituteExprs subst l) (substituteExprs subst r) pos
  Unary op e pos -> Unary op (substituteExprs subst e) pos
  Ternary c t e pos ->
    Ternary (substituteExprs subst c) (substituteExprs subst t) (substituteExprs subst e) pos
  Call name args pos -> Call name (map (substituteExprs subst) args) pos
  InstanceCall target method args pos ->
    InstanceCall (substituteExprs subst target) method (map (substituteExprs subst) args) pos
  NewObject cn args pos -> NewObject cn (map (substituteExprs subst) args) pos
  FieldAccess target field pos -> FieldAccess (substituteExprs subst target) field pos
  e -> e

--------------------------------------------------------------------------------
-- Loop Fusion
--------------------------------------------------------------------------------

-- | Fuse adjacent loops with the same bounds.
-- while (i < n) { A; i++; } while (j < n) { B; j++; }
-- becomes: while (i < n) { A; B; i++; }
fuseLoops :: Program -> Program
fuseLoops (Program classes) = Program (map fuseClass classes)

fuseClass :: ClassDecl -> ClassDecl
fuseClass cls@ClassDecl{..} = cls { classMethods = map fuseMethod classMethods }

fuseMethod :: MethodDecl -> MethodDecl
fuseMethod m@MethodDecl{..} = m { methodBody = fuseStmt methodBody }

fuseStmt :: Stmt -> Stmt
fuseStmt = \case
  Block stmts pos -> Block (fuseBlock stmts) pos
  If cond th el pos -> If cond (fuseStmt th) (fuseStmt el) pos
  While cond body pos -> While cond (fuseStmt body) pos
  s -> s

fuseBlock :: [Stmt] -> [Stmt]
fuseBlock [] = []
fuseBlock [s] = [fuseStmt s]
fuseBlock (s1 : s2 : rest) = case (s1, s2) of
  -- Pattern: two while loops with same bound
  (While cond1 body1 pos1, While cond2 body2 _)
    | Just (var1, bound1) <- getLoopBound cond1
    , Just (var2, bound2) <- getLoopBound cond2
    , bound1 == bound2
    , Just incr1 <- getLoopIncrement var1 body1
    , Just incr2 <- getLoopIncrement var2 body2
    , incr1 == incr2 && incr1 == 1
    , var1 == var2  -- Same loop variable
    ->
      let -- Merge bodies (excluding increments)
          body1' = removeIncrement var1 body1
          body2' = removeIncrement var2 body2
          merged = mergeLoopBodies body1' body2'
          -- Add single increment at end
          newBody = addIncrement var1 merged
      in fuseBlock (While cond1 newBody pos1 : rest)

  _ -> fuseStmt s1 : fuseBlock (s2 : rest)

mergeLoopBodies :: Stmt -> Stmt -> Stmt
mergeLoopBodies (Block s1 pos) (Block s2 _) = Block (s1 ++ s2) pos
mergeLoopBodies (Block s1 pos) s2 = Block (s1 ++ [s2]) pos
mergeLoopBodies s1 (Block s2 pos) = Block (s1 : s2) pos
mergeLoopBodies s1 s2 = Block [s1, s2] 0

addIncrement :: String -> Stmt -> Stmt
addIncrement name (Block stmts pos) =
  Block (stmts ++ [Assign name (Binary Add (Var name 0) (IntLit 1 0) 0) 0]) pos
addIncrement name s = Block [s, Assign name (Binary Add (Var name 0) (IntLit 1 0) 0) 0] 0
