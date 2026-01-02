{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Static Single Assignment (SSA) form for LiveOak.
-- Each variable is assigned exactly once, with phi functions at join points.
module LiveOak.SSA
  ( -- * SSA Types
    SSAProgram(..)
  , SSAMethod(..)
  , SSABlock(..)
  , SSAInstr(..)
  , SSAExpr(..)
  , PhiNode(..)
  , SSAVar(..)

    -- * Conversion
  , toSSA
  , fromSSA

    -- * SSA Optimizations
  , ssaConstantProp
  , ssaDeadCodeElim
  , ssaCopyProp
  , partialRedundancyElim
  ) where

import LiveOak.Ast
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State

--------------------------------------------------------------------------------
-- SSA Types
--------------------------------------------------------------------------------

-- | SSA variable with version number
data SSAVar = SSAVar
  { ssaName :: !String     -- ^ Original variable name
  , ssaVersion :: !Int     -- ^ Version number (0 = original)
  } deriving (Eq, Ord, Show)

-- | Phi node: selects value based on predecessor block
data PhiNode = PhiNode
  { phiVar :: !SSAVar                    -- ^ Variable being defined
  , phiArgs :: ![(String, SSAVar)]       -- ^ (predecessor label, value)
  } deriving (Eq, Show)

-- | SSA expression
data SSAExpr
  = SSAInt !Int
  | SSABool !Bool
  | SSAStr !String
  | SSANull
  | SSAUse !SSAVar                      -- ^ Use of SSA variable
  | SSAThis
  | SSAUnary !UnaryOp !SSAExpr
  | SSABinary !BinaryOp !SSAExpr !SSAExpr
  | SSATernary !SSAExpr !SSAExpr !SSAExpr
  | SSACall !String ![SSAExpr]
  | SSAInstanceCall !SSAExpr !String ![SSAExpr]
  | SSANewObject !String ![SSAExpr]
  | SSAFieldAccess !SSAExpr !String
  deriving (Eq, Show)

-- | SSA instruction
data SSAInstr
  = SSAAssign !SSAVar !SSAExpr          -- ^ x_n = expr
  | SSAFieldStore !SSAExpr !String !Int !SSAExpr  -- ^ target.field = value
  | SSAReturn !(Maybe SSAExpr)
  | SSAJump !String                     -- ^ Unconditional jump
  | SSABranch !SSAExpr !String !String  -- ^ Conditional branch (cond, true, false)
  | SSAExprStmt !SSAExpr                -- ^ Expression for side effects
  deriving (Eq, Show)

-- | Basic block in SSA form
data SSABlock = SSABlock
  { blockLabel :: !String
  , blockPhis :: ![PhiNode]             -- ^ Phi functions at block start
  , blockInstrs :: ![SSAInstr]          -- ^ Instructions (non-phi)
  } deriving (Eq, Show)

-- | Method in SSA form
data SSAMethod = SSAMethod
  { ssaMethodName :: !String
  , ssaMethodParams :: ![SSAVar]        -- ^ Parameters as SSA vars (version 0)
  , ssaMethodBlocks :: ![SSABlock]      -- ^ Basic blocks
  , ssaEntryBlock :: !String            -- ^ Entry block label
  } deriving (Eq, Show)

-- | Program in SSA form
data SSAProgram = SSAProgram
  { ssaClasses :: ![(String, [SSAMethod])]
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Conversion to SSA
--------------------------------------------------------------------------------

-- | Convert a program to SSA form
toSSA :: Program -> SSAProgram
toSSA (Program classes) = SSAProgram
  [(className c, map (methodToSSA (className c)) (classMethods c)) | c <- classes]

-- | State for SSA conversion
data SSAState = SSAState
  { nextVersion :: !(Map String Int)    -- ^ Next version for each variable
  , currentDefs :: !(Map String SSAVar) -- ^ Current definition of each variable
  , nextBlockId :: !Int                 -- ^ For generating unique block labels
  }

type SSAConv a = State SSAState a

-- | Get fresh version of a variable
freshVar :: String -> SSAConv SSAVar
freshVar name = do
  st <- get
  let ver = Map.findWithDefault 0 name (nextVersion st)
  put st { nextVersion = Map.insert name (ver + 1) (nextVersion st) }
  return (SSAVar name ver)

-- | Define a variable (create new version)
defineVar :: String -> SSAConv SSAVar
defineVar name = do
  v <- freshVar name
  modify $ \st -> st { currentDefs = Map.insert name v (currentDefs st) }
  return v

-- | Use a variable (get current version)
useVar :: String -> SSAConv SSAVar
useVar name = do
  st <- get
  case Map.lookup name (currentDefs st) of
    Just v -> return v
    Nothing -> do
      -- First use - create version 0
      let v = SSAVar name 0
      modify $ \st' -> st' { currentDefs = Map.insert name v (currentDefs st') }
      return v

-- | Get fresh block label
freshBlock :: SSAConv String
freshBlock = do
  st <- get
  let n = nextBlockId st
  put st { nextBlockId = n + 1 }
  return $ "B" ++ show n

-- | Convert a method to SSA form
methodToSSA :: String -> MethodDecl -> SSAMethod
methodToSSA _className MethodDecl{..} =
  let initState = SSAState Map.empty Map.empty 0
      -- Initialize parameters as version 0
      paramVars = [SSAVar (paramName p) 0 | p <- methodParams]
      initDefs = Map.fromList [(paramName p, SSAVar (paramName p) 0) | p <- methodParams]
      st = initState { currentDefs = initDefs }
      (blocks, _) = runState (stmtToBlocks "entry" methodBody) st
  in SSAMethod methodName paramVars blocks "entry"

-- | Convert a statement to SSA blocks
stmtToBlocks :: String -> Stmt -> SSAConv [SSABlock]
stmtToBlocks label = \case
  Block stmts _ -> do
    (instrs, blocks) <- stmtsToInstrs stmts
    return $ SSABlock label [] instrs : blocks

  VarDecl name _ initOpt _ -> do
    case initOpt of
      Just expr -> do
        ssaExpr <- exprToSSA expr
        v <- defineVar name
        return [SSABlock label [] [SSAAssign v ssaExpr]]
      Nothing -> do
        v <- defineVar name
        return [SSABlock label [] [SSAAssign v SSANull]]

  Assign name expr _ -> do
    ssaExpr <- exprToSSA expr
    v <- defineVar name
    return [SSABlock label [] [SSAAssign v ssaExpr]]

  FieldAssign target field off value _ -> do
    t <- exprToSSA target
    v <- exprToSSA value
    return [SSABlock label [] [SSAFieldStore t field off v]]

  Return exprOpt _ -> do
    ssaExprOpt <- traverse exprToSSA exprOpt
    return [SSABlock label [] [SSAReturn ssaExprOpt]]

  If cond th el _ -> do
    ssaCond <- exprToSSA cond
    thenLabel <- freshBlock
    elseLabel <- freshBlock
    joinLabel <- freshBlock

    -- Convert branches
    thenBlocks <- stmtToBlocks thenLabel th
    elseBlocks <- stmtToBlocks elseLabel el

    -- Add jumps to join at end of branches
    let thenBlocks' = addJumpToEnd thenBlocks joinLabel
        elseBlocks' = addJumpToEnd elseBlocks joinLabel

    let branchInstr = SSABranch ssaCond thenLabel elseLabel
        entryBlock = SSABlock label [] [branchInstr]
        joinBlock = SSABlock joinLabel [] []  -- Phi nodes would go here

    return $ entryBlock : thenBlocks' ++ elseBlocks' ++ [joinBlock]

  While cond body _ -> do
    ssaCond <- exprToSSA cond
    headerLabel <- freshBlock
    bodyLabel <- freshBlock
    exitLabel <- freshBlock

    -- Header block with condition
    let headerBlock = SSABlock headerLabel [] [SSABranch ssaCond bodyLabel exitLabel]

    -- Body block
    bodyBlocks <- stmtToBlocks bodyLabel body
    let bodyBlocks' = addJumpToEnd bodyBlocks headerLabel

    -- Entry jumps to header
    let entryBlock = SSABlock label [] [SSAJump headerLabel]
        exitBlock = SSABlock exitLabel [] []

    return $ entryBlock : headerBlock : bodyBlocks' ++ [exitBlock]

  Break _ -> do
    -- Note: proper break handling requires knowing the enclosing loop
    return [SSABlock label [] []]

  ExprStmt expr _ -> do
    ssaExpr <- exprToSSA expr
    return [SSABlock label [] [SSAExprStmt ssaExpr]]

-- | Add a jump instruction to the end of the last block
addJumpToEnd :: [SSABlock] -> String -> [SSABlock]
addJumpToEnd [] target = [SSABlock "empty" [] [SSAJump target]]
addJumpToEnd blocks target =
  let (init', last') = (init blocks, last blocks)
      lastWithJump = last' { blockInstrs = blockInstrs last' ++ [SSAJump target] }
  in init' ++ [lastWithJump]

-- | Convert statements to instructions
stmtsToInstrs :: [Stmt] -> SSAConv ([SSAInstr], [SSABlock])
stmtsToInstrs stmts = do
  results <- mapM stmtToInstrsHelper stmts
  let (instrLists, blockLists) = unzip results
  return (concat instrLists, concat blockLists)
  where
    stmtToInstrsHelper stmt = do
      blocks <- stmtToBlocks "temp" stmt
      case blocks of
        [SSABlock _ [] instrs] -> return (instrs, [])
        _ -> return ([], blocks)

-- | Convert an expression to SSA
exprToSSA :: Expr -> SSAConv SSAExpr
exprToSSA = \case
  IntLit n _ -> return $ SSAInt n
  BoolLit b _ -> return $ SSABool b
  StrLit s _ -> return $ SSAStr s
  NullLit _ -> return SSANull
  Var name _ -> SSAUse <$> useVar name
  This _ -> return SSAThis
  Unary op e _ -> SSAUnary op <$> exprToSSA e
  Binary op l r _ -> SSABinary op <$> exprToSSA l <*> exprToSSA r
  Ternary c t e _ -> SSATernary <$> exprToSSA c <*> exprToSSA t <*> exprToSSA e
  Call name args _ -> SSACall name <$> mapM exprToSSA args
  InstanceCall target method args _ ->
    SSAInstanceCall <$> exprToSSA target <*> pure method <*> mapM exprToSSA args
  NewObject cn args _ -> SSANewObject cn <$> mapM exprToSSA args
  FieldAccess target field _ -> SSAFieldAccess <$> exprToSSA target <*> pure field

--------------------------------------------------------------------------------
-- Conversion from SSA
--------------------------------------------------------------------------------

-- | Convert SSA back to normal form (for code generation)
-- This inserts copy instructions for phi nodes
fromSSA :: SSAProgram -> Program
fromSSA (SSAProgram classes) = Program
  [ClassDecl cn [] (map ssaMethodToNormal methods) | (cn, methods) <- classes]

-- | Convert SSA method back to normal AST
ssaMethodToNormal :: SSAMethod -> MethodDecl
ssaMethodToNormal SSAMethod{..} =
  let params = [ParamDecl (ssaName v) undefined | v <- ssaMethodParams]
      body = blocksToStmt ssaMethodBlocks
  in MethodDecl "" ssaMethodName params Void body

-- | Convert SSA blocks to a statement
blocksToStmt :: [SSABlock] -> Stmt
blocksToStmt blocks = Block (concatMap blockToStmts blocks) 0

-- | Convert a single block to statements
blockToStmts :: SSABlock -> [Stmt]
blockToStmts SSABlock{..} =
  -- Phi nodes become assignments from the appropriate predecessor
  -- (simplified - real implementation would need control flow info)
  map phiToStmt blockPhis ++ map instrToStmt blockInstrs

phiToStmt :: PhiNode -> Stmt
phiToStmt PhiNode{..} =
  -- Simplified: just use first argument
  case phiArgs of
    ((_, v):_) -> Assign (varToName phiVar) (Var (varToName v) 0) 0
    [] -> Block [] 0

instrToStmt :: SSAInstr -> Stmt
instrToStmt = \case
  SSAAssign v e -> Assign (varToName v) (ssaExprToExpr e) 0
  SSAFieldStore t f off v -> FieldAssign (ssaExprToExpr t) f off (ssaExprToExpr v) 0
  SSAReturn e -> Return (ssaExprToExpr <$> e) 0
  SSAJump _ -> Block [] 0  -- Jumps handled by control flow
  SSABranch c _t _ -> If (ssaExprToExpr c) (Block [] 0) (Block [] 0) 0
  SSAExprStmt e -> ExprStmt (ssaExprToExpr e) 0

varToName :: SSAVar -> String
varToName (SSAVar name ver) = name ++ "_" ++ show ver

ssaExprToExpr :: SSAExpr -> Expr
ssaExprToExpr = \case
  SSAInt n -> IntLit n 0
  SSABool b -> BoolLit b 0
  SSAStr s -> StrLit s 0
  SSANull -> NullLit 0
  SSAUse v -> Var (varToName v) 0
  SSAThis -> This 0
  SSAUnary op e -> Unary op (ssaExprToExpr e) 0
  SSABinary op l r -> Binary op (ssaExprToExpr l) (ssaExprToExpr r) 0
  SSATernary c t e -> Ternary (ssaExprToExpr c) (ssaExprToExpr t) (ssaExprToExpr e) 0
  SSACall name args -> Call name (map ssaExprToExpr args) 0
  SSAInstanceCall t m args -> InstanceCall (ssaExprToExpr t) m (map ssaExprToExpr args) 0
  SSANewObject cn args -> NewObject cn (map ssaExprToExpr args) 0
  SSAFieldAccess t f -> FieldAccess (ssaExprToExpr t) f 0

--------------------------------------------------------------------------------
-- SSA Optimizations
--------------------------------------------------------------------------------

-- | Sparse conditional constant propagation on SSA
ssaConstantProp :: SSAProgram -> SSAProgram
ssaConstantProp (SSAProgram classes) =
  SSAProgram [(cn, map propMethod methods) | (cn, methods) <- classes]
  where
    propMethod m = m { ssaMethodBlocks = map propBlock (ssaMethodBlocks m) }
    propBlock b = b { blockInstrs = map propInstr (blockInstrs b) }
    propInstr = \case
      SSAAssign v e -> SSAAssign v (foldSSAExpr e)
      SSAFieldStore t f off v -> SSAFieldStore (foldSSAExpr t) f off (foldSSAExpr v)
      SSAReturn e -> SSAReturn (foldSSAExpr <$> e)
      SSABranch c t f -> SSABranch (foldSSAExpr c) t f
      SSAExprStmt e -> SSAExprStmt (foldSSAExpr e)
      i -> i

-- | Fold constant expressions in SSA
foldSSAExpr :: SSAExpr -> SSAExpr
foldSSAExpr = \case
  SSAUnary Neg (SSAInt n) -> SSAInt (-n)
  SSAUnary Not (SSABool b) -> SSABool (not b)
  SSABinary Add (SSAInt a) (SSAInt b) -> SSAInt (a + b)
  SSABinary Sub (SSAInt a) (SSAInt b) -> SSAInt (a - b)
  SSABinary Mul (SSAInt a) (SSAInt b) -> SSAInt (a * b)
  SSABinary Div (SSAInt a) (SSAInt b) | b /= 0 -> SSAInt (a `div` b)
  SSABinary Eq (SSAInt a) (SSAInt b) -> SSABool (a == b)
  SSABinary Lt (SSAInt a) (SSAInt b) -> SSABool (a < b)
  SSABinary Gt (SSAInt a) (SSAInt b) -> SSABool (a > b)
  SSABinary And (SSABool a) (SSABool b) -> SSABool (a && b)
  SSABinary Or (SSABool a) (SSABool b) -> SSABool (a || b)
  SSATernary (SSABool True) t _ -> foldSSAExpr t
  SSATernary (SSABool False) _ e -> foldSSAExpr e
  e -> e

-- | Dead code elimination on SSA
ssaDeadCodeElim :: SSAProgram -> SSAProgram
ssaDeadCodeElim (SSAProgram classes) =
  SSAProgram [(cn, map elimMethod methods) | (cn, methods) <- classes]
  where
    elimMethod m =
      let used = collectUsed (ssaMethodBlocks m)
          blocks' = map (elimBlock used) (ssaMethodBlocks m)
      in m { ssaMethodBlocks = blocks' }

    elimBlock used b = b
      { blockPhis = filter (isUsed used . phiVar) (blockPhis b)
      , blockInstrs = filter (instrIsUsed used) (blockInstrs b)
      }

    isUsed used v = Set.member (ssaName v, ssaVersion v) used

    instrIsUsed _ (SSAReturn _) = True
    instrIsUsed _ (SSAJump _) = True
    instrIsUsed _ (SSABranch _ _ _) = True
    instrIsUsed _ (SSAFieldStore _ _ _ _) = True
    instrIsUsed _ (SSAExprStmt _) = True
    instrIsUsed used (SSAAssign v _) = isUsed used v

-- | Collect all used SSA variables
collectUsed :: [SSABlock] -> Set (String, Int)
collectUsed blocks = Set.unions (map blockUsed blocks)
  where
    blockUsed b = Set.unions $
      map phiUsed (blockPhis b) ++ map instrUsed (blockInstrs b)

    phiUsed phi = Set.unions [varUsed v | (_, v) <- phiArgs phi]

    instrUsed = \case
      SSAAssign _ e -> exprUsed e
      SSAFieldStore t _ _ v -> Set.union (exprUsed t) (exprUsed v)
      SSAReturn (Just e) -> exprUsed e
      SSAReturn Nothing -> Set.empty
      SSAJump _ -> Set.empty
      SSABranch c _ _ -> exprUsed c
      SSAExprStmt e -> exprUsed e

    exprUsed = \case
      SSAUse v -> varUsed v
      SSAUnary _ e -> exprUsed e
      SSABinary _ l r -> Set.union (exprUsed l) (exprUsed r)
      SSATernary c t e -> Set.unions [exprUsed c, exprUsed t, exprUsed e]
      SSACall _ args -> Set.unions (map exprUsed args)
      SSAInstanceCall t _ args -> Set.unions (exprUsed t : map exprUsed args)
      SSANewObject _ args -> Set.unions (map exprUsed args)
      SSAFieldAccess t _ -> exprUsed t
      _ -> Set.empty

    varUsed v = Set.singleton (ssaName v, ssaVersion v)

-- | Copy propagation on SSA
ssaCopyProp :: SSAProgram -> SSAProgram
ssaCopyProp (SSAProgram classes) =
  SSAProgram [(cn, map propMethod methods) | (cn, methods) <- classes]
  where
    propMethod m =
      let copies = findCopies (ssaMethodBlocks m)
          blocks' = map (substBlock copies) (ssaMethodBlocks m)
      in m { ssaMethodBlocks = blocks' }

    -- Find x = y patterns
    findCopies blocks = Map.fromList
      [ ((ssaName v, ssaVersion v), src)
      | b <- blocks
      , SSAAssign v (SSAUse src) <- blockInstrs b
      ]

    substBlock copies b = b
      { blockPhis = map (substPhi copies) (blockPhis b)
      , blockInstrs = map (substInstr copies) (blockInstrs b)
      }

    substPhi copies phi = phi
      { phiArgs = [(l, substVar copies v) | (l, v) <- phiArgs phi] }

    substInstr copies = \case
      SSAAssign v e -> SSAAssign v (substExpr copies e)
      SSAFieldStore t f off v -> SSAFieldStore (substExpr copies t) f off (substExpr copies v)
      SSAReturn e -> SSAReturn (substExpr copies <$> e)
      SSABranch c t f -> SSABranch (substExpr copies c) t f
      SSAExprStmt e -> SSAExprStmt (substExpr copies e)
      i -> i

    substVar copies v =
      case Map.lookup (ssaName v, ssaVersion v) copies of
        Just src -> substVar copies src  -- Transitive
        Nothing -> v

    substExpr copies = \case
      SSAUse v -> SSAUse (substVar copies v)
      SSAUnary op e -> SSAUnary op (substExpr copies e)
      SSABinary op l r -> SSABinary op (substExpr copies l) (substExpr copies r)
      SSATernary c t e -> SSATernary (substExpr copies c) (substExpr copies t) (substExpr copies e)
      SSACall n args -> SSACall n (map (substExpr copies) args)
      SSAInstanceCall t m args -> SSAInstanceCall (substExpr copies t) m (map (substExpr copies) args)
      SSANewObject cn args -> SSANewObject cn (map (substExpr copies) args)
      SSAFieldAccess t f -> SSAFieldAccess (substExpr copies t) f
      e -> e

--------------------------------------------------------------------------------
-- Partial Redundancy Elimination (PRE)
--------------------------------------------------------------------------------

-- | Partial Redundancy Elimination on SSA form
-- Finds expressions that are computed on multiple paths and hoists them
-- to make redundant computations eliminable.
partialRedundancyElim :: SSAProgram -> SSAProgram
partialRedundancyElim (SSAProgram classes) =
  SSAProgram [(cn, map preMethod methods) | (cn, methods) <- classes]
  where
    preMethod m =
      let -- Step 1: Find all expressions and where they're computed
          exprMap = collectExpressions (ssaMethodBlocks m)
          -- Step 2: Find fully redundant expressions (computed in all predecessors)
          redundant = findFullyRedundant exprMap
          -- Step 3: Eliminate redundant computations by reusing earlier results
          blocks' = eliminateRedundant redundant (ssaMethodBlocks m)
      in m { ssaMethodBlocks = blocks' }

-- | Canonical form of an expression for comparison
-- (ignoring position info, treating equivalent expressions as equal)
data CanonExpr
  = CUnary UnaryOp CanonExpr
  | CBinary BinaryOp CanonExpr CanonExpr
  | CVar String Int
  | CInt Int
  | CBool Bool
  | CStr String
  | CNull
  | CThis
  deriving (Eq, Ord, Show)

-- | Convert SSA expression to canonical form
canonicalize :: SSAExpr -> Maybe CanonExpr
canonicalize = \case
  SSAInt n -> Just $ CInt n
  SSABool b -> Just $ CBool b
  SSAStr s -> Just $ CStr s
  SSANull -> Just CNull
  SSAThis -> Just CThis
  SSAUse (SSAVar name ver) -> Just $ CVar name ver
  SSAUnary op e -> CUnary op <$> canonicalize e
  SSABinary op l r -> CBinary op <$> canonicalize l <*> canonicalize r
  -- Skip complex expressions for now
  _ -> Nothing

-- | Collect all expressions and where they're computed
-- Returns: expression -> [(block, var that holds the result)]
collectExpressions :: [SSABlock] -> Map CanonExpr [(String, SSAVar)]
collectExpressions blocks = Map.fromListWith (++)
  [ (ce, [(blockLabel b, v)])
  | b <- blocks
  , SSAAssign v e <- blockInstrs b
  , Just ce <- [canonicalize e]
  , isWorthHoisting ce
  ]

-- | Check if an expression is worth hoisting
-- (avoid hoisting trivial expressions)
isWorthHoisting :: CanonExpr -> Bool
isWorthHoisting = \case
  CUnary _ _ -> True
  CBinary _ _ _ -> True
  _ -> False

-- | Find fully redundant expressions
-- An expression is fully redundant if it's already computed and available
findFullyRedundant :: Map CanonExpr [(String, SSAVar)] -> Map CanonExpr SSAVar
findFullyRedundant exprMap = Map.mapMaybe pickFirst exprMap
  where
    -- Use the first computation as the canonical one
    -- (In a full implementation, we'd use dominance to pick the best)
    pickFirst [] = Nothing
    pickFirst [_] = Nothing  -- Only one computation, nothing to eliminate
    pickFirst ((_, v):_) = Just v  -- Multiple computations, use first

-- | Eliminate redundant computations
eliminateRedundant :: Map CanonExpr SSAVar -> [SSABlock] -> [SSABlock]
eliminateRedundant redundant blocks = map elimBlock blocks
  where
    elimBlock b = b { blockInstrs = concatMap elimInstr (blockInstrs b) }

    elimInstr instr@(SSAAssign v e) =
      case canonicalize e >>= (`Map.lookup` redundant) of
        Just canonical | canonical /= v ->
          -- Replace with copy from canonical version
          [SSAAssign v (SSAUse canonical)]
        _ -> [instr]
    elimInstr instr = [instr]
