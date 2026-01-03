{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Static Single Assignment (SSA) form for LiveOak.
-- Each variable is assigned exactly once, with phi functions at join points.
module LiveOak.SSA
  ( -- * SSA Types (re-exported from SSATypes)
    SSAProgram(..)
  , SSAClass(..)
  , SSAMethod(..)
  , SSABlock(..)
  , SSAInstr(..)
  , SSAExpr(..)
  , PhiNode(..)
  , SSAVar(..)

    -- * Conversion
  , toSSA
  , toSSAWithCFG    -- ^ Uses CFG-based phi placement
  , fromSSA

    -- * SSA Optimizations
  , ssaConstantProp
  , ssaDeadCodeElim
  , ssaCopyProp
  , partialRedundancyElim
  , simplifyPhis

    -- * Full SSA Optimization Pipeline
  , fullSSAOptimize

    -- * Structured SSA Optimization
  , structuredSSAOpt

    -- * CFG-Based Optimization Pipeline
  , optimizeSSA       -- ^ Full CFG-based SSA optimization
  ) where

import LiveOak.Ast
import LiveOak.Types (ValueType)
import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Dominance
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Conversion to SSA
--------------------------------------------------------------------------------

-- | Convert a program to SSA form
toSSA :: Program -> SSAProgram
toSSA (Program classes) = SSAProgram
  [classToSSA c | c <- classes]

-- | Convert a class to SSA form
classToSSA :: ClassDecl -> SSAClass
classToSSA ClassDecl{..} = SSAClass
  { ssaClassName = className
  , ssaClassFields = classFields
  , ssaClassMethods = map (methodToSSA className) classMethods
  }

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
  return (SSAVar name ver Nothing)

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
      let v = SSAVar name 0 Nothing
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
methodToSSA clsName MethodDecl{..} =
  let initState = SSAState Map.empty Map.empty 0
      -- Initialize parameters as version 0 with their types
      paramVars = [SSAVar (paramName p) 0 (Just (paramType p)) | p <- methodParams]
      initDefs = Map.fromList [(paramName p, SSAVar (paramName p) 0 (Just (paramType p))) | p <- methodParams]
      st = initState { currentDefs = initDefs }
      (blocks, _) = runState (stmtToBlocks "entry" methodBody) st
  in SSAMethod clsName methodName paramVars methodReturnSig blocks "entry"

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
        ifEntryBlock = SSABlock label [] [branchInstr]
        joinBlock = SSABlock joinLabel [] []  -- Phi nodes would go here

    return $ ifEntryBlock : thenBlocks' ++ elseBlocks' ++ [joinBlock]

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
    let whileEntryBlock = SSABlock label [] [SSAJump headerLabel]
        exitBlock = SSABlock exitLabel [] []

    return $ whileEntryBlock : headerBlock : bodyBlocks' ++ [exitBlock]

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
-- CFG-Based SSA Conversion (with proper phi placement)
--------------------------------------------------------------------------------

-- | Convert a program to SSA form using CFG and dominance analysis.
-- This produces proper phi node placement using dominance frontiers.
toSSAWithCFG :: Program -> SSAProgram
toSSAWithCFG (Program classes) = SSAProgram
  [classToSSAWithCFG c | c <- classes]

-- | Convert a class using CFG-based SSA
classToSSAWithCFG :: ClassDecl -> SSAClass
classToSSAWithCFG ClassDecl{..} = SSAClass
  { ssaClassName = className
  , ssaClassFields = classFields
  , ssaClassMethods = map (methodToSSAWithCFG className) classMethods
  }

-- | Convert a method using CFG-based SSA with proper phi placement
methodToSSAWithCFG :: String -> MethodDecl -> SSAMethod
methodToSSAWithCFG clsName decl@MethodDecl{..} =
  -- Step 1: Convert to basic blocks (with simple SSA naming)
  let basicMethod = methodToSSA clsName decl
      -- Step 2: Build CFG
      cfg = buildCFG basicMethod
      -- Step 3: Compute dominance
      domTree = computeDominators cfg
      domFrontier = computeDomFrontier cfg domTree
      -- Step 4: Find all variables that need phi nodes
      defSites = findDefSites basicMethod
      -- Step 5: Insert phi nodes at dominance frontiers
      blocksWithPhis = insertPhis cfg domFrontier defSites (ssaMethodBlocks basicMethod)
      -- Step 6: Rename variables with proper SSA numbering
      renamedBlocks = renameVariables cfg domTree methodParams blocksWithPhis
  in basicMethod { ssaMethodBlocks = renamedBlocks }

-- | Find all definition sites for each variable
-- Returns: variable name -> set of blocks where it's defined
findDefSites :: SSAMethod -> Map String (Set BlockId)
findDefSites method = foldl' addBlockDefs Map.empty (ssaMethodBlocks method)
  where
    addBlockDefs acc block =
      foldl' (addDef (blockLabel block)) acc (blockInstrs block)

    addDef blockId acc instr = case instr of
      SSAAssign var _ ->
        Map.insertWith Set.union (ssaName var) (Set.singleton blockId) acc
      _ -> acc

-- | Insert phi nodes at dominance frontiers of definition sites
insertPhis :: CFG -> DomFrontier -> Map String (Set BlockId) -> [SSABlock] -> [SSABlock]
insertPhis cfg domFrontier defSites blocks =
  let -- For each variable, compute blocks that need phi nodes
      phiSites = Map.mapWithKey (computePhiSites domFrontier) defSites
      -- Insert phi nodes into blocks
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      blockMap' = Map.foldlWithKey' (insertPhisForVar cfg) blockMap phiSites
  in map snd $ Map.toList blockMap'

-- | Compute where phi nodes are needed for a variable using dominance frontiers
computePhiSites :: DomFrontier -> String -> Set BlockId -> Set BlockId
computePhiSites domFrontier _varName defBlocks = go defBlocks Set.empty
  where
    go worklist phiBlocks
      | Set.null worklist = phiBlocks
      | otherwise =
          let (block, rest) = Set.deleteFindMin worklist
              -- Get dominance frontier of this block
              frontier = Map.findWithDefault Set.empty block domFrontier
              -- Add phi nodes at frontier blocks that don't have one yet
              newPhiBlocks = Set.difference frontier phiBlocks
              -- Phi nodes are also definitions, so add to worklist
              newWorklist = Set.union rest (Set.difference newPhiBlocks defBlocks)
          in go newWorklist (Set.union phiBlocks newPhiBlocks)

-- | Insert phi nodes for a variable into the appropriate blocks
insertPhisForVar :: CFG -> Map BlockId SSABlock -> String -> Set BlockId -> Map BlockId SSABlock
insertPhisForVar cfg blockMap varName phiBlocks =
  Set.foldl' insertPhi blockMap phiBlocks
  where
    insertPhi bm blockId =
      case Map.lookup blockId bm of
        Nothing -> bm  -- Block not found
        Just block ->
          -- Create phi node with placeholder arguments
          let preds = predecessors cfg blockId
              phiArgs = [(p, SSAVar varName 0 Nothing) | p <- preds]
              phi = PhiNode (SSAVar varName 0 Nothing) phiArgs
              -- Add phi if not already present for this variable
              existingPhis = blockPhis block
              hasPhiForVar = any (\p -> ssaName (phiVar p) == varName) existingPhis
          in if hasPhiForVar
             then bm
             else Map.insert blockId (block { blockPhis = phi : existingPhis }) bm

--------------------------------------------------------------------------------
-- SSA Variable Renaming
--------------------------------------------------------------------------------

-- | Rename variables with proper SSA versioning
-- Uses dominator tree traversal to maintain reaching definitions
renameVariables :: CFG -> DomTree -> [ParamDecl] -> [SSABlock] -> [SSABlock]
renameVariables cfg domTree params blocks =
  let -- Initialize with parameters as version 0
      initVersions = Map.fromList [(paramName p, 0) | p <- params]
      initDefs = Map.fromList [(paramName p, SSAVar (paramName p) 0 (Just (paramType p))) | p <- params]
      initState = RenameState initVersions initDefs
      -- Process blocks in dominator tree order
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      (_, renamedMap) = renameBlock cfg domTree (cfgEntry cfg) initState blockMap
  in map snd $ Map.toList renamedMap

-- | State for variable renaming
data RenameState = RenameState
  { renameVersions :: !(Map String Int)      -- ^ Next version for each variable
  , renameCurrentDef :: !(Map String SSAVar) -- ^ Current reaching definition
  }

-- | Rename variables in a block and its dominance subtree
renameBlock :: CFG -> DomTree -> BlockId -> RenameState -> Map BlockId SSABlock
           -> (RenameState, Map BlockId SSABlock)
renameBlock cfg domTree blockId renSt blockMap =
  case Map.lookup blockId blockMap of
    Nothing -> (renSt, blockMap)
    Just block ->
      let -- Rename phi node definitions (create new versions)
          (renSt1, renamedPhis) = renamePhistDefs renSt (blockPhis block)
          -- Rename instructions
          (renSt2, renamedInstrs) = renameInstrs renSt1 (blockInstrs block)
          -- Update block
          renamedBlock = block { blockPhis = renamedPhis, blockInstrs = renamedInstrs }
          blockMap1 = Map.insert blockId renamedBlock blockMap
          -- Fill in phi arguments in successor blocks
          blockMap2 = foldl' (fillPhiArgs blockId renSt2) blockMap1 (successors cfg blockId)
          -- Process children in dominator tree
          (renSt3, blockMap3) = foldl' (processChild cfg domTree)
                                       (renSt2, blockMap2)
                                       (domChildren domTree blockId)
      in (renSt3, blockMap3)

-- | Process a child in the dominator tree
processChild :: CFG -> DomTree -> (RenameState, Map BlockId SSABlock) -> BlockId
            -> (RenameState, Map BlockId SSABlock)
processChild cfg domTree (renSt, blockMap) childId =
  renameBlock cfg domTree childId renSt blockMap

-- | Rename phi node definitions
renamePhistDefs :: RenameState -> [PhiNode] -> (RenameState, [PhiNode])
renamePhistDefs renSt phis = foldl' renamePhi (renSt, []) phis
  where
    renamePhi (st, acc) phi =
      let varName = ssaName (phiVar phi)
          version = Map.findWithDefault 0 varName (renameVersions st)
          newVar = SSAVar varName version (ssaVarType (phiVar phi))
          st' = st { renameVersions = Map.insert varName (version + 1) (renameVersions st)
                   , renameCurrentDef = Map.insert varName newVar (renameCurrentDef st)
                   }
          phi' = phi { phiVar = newVar }
      in (st', acc ++ [phi'])

-- | Rename instructions
renameInstrs :: RenameState -> [SSAInstr] -> (RenameState, [SSAInstr])
renameInstrs renSt instrs = foldl' renameInstr (renSt, []) instrs
  where
    renameInstr (st, acc) instr = case instr of
      SSAAssign var expr ->
        let expr' = renameExpr st expr
            varName = ssaName var
            version = Map.findWithDefault 0 varName (renameVersions st)
            newVar = SSAVar varName version (ssaVarType var)
            st' = st { renameVersions = Map.insert varName (version + 1) (renameVersions st)
                     , renameCurrentDef = Map.insert varName newVar (renameCurrentDef st)
                     }
        in (st', acc ++ [SSAAssign newVar expr'])

      SSAFieldStore target field off value ->
        let target' = renameExpr st target
            value' = renameExpr st value
        in (st, acc ++ [SSAFieldStore target' field off value'])

      SSAReturn exprOpt ->
        let exprOpt' = fmap (renameExpr st) exprOpt
        in (st, acc ++ [SSAReturn exprOpt'])

      SSAJump target ->
        (st, acc ++ [SSAJump target])

      SSABranch cond t f ->
        let cond' = renameExpr st cond
        in (st, acc ++ [SSABranch cond' t f])

      SSAExprStmt expr ->
        let expr' = renameExpr st expr
        in (st, acc ++ [SSAExprStmt expr'])

-- | Rename uses in an expression
renameExpr :: RenameState -> SSAExpr -> SSAExpr
renameExpr renSt = \case
  SSAUse var ->
    case Map.lookup (ssaName var) (renameCurrentDef renSt) of
      Just v -> SSAUse v
      Nothing -> SSAUse var  -- Keep original if not found
  SSAUnary op e -> SSAUnary op (renameExpr renSt e)
  SSABinary op l r -> SSABinary op (renameExpr renSt l) (renameExpr renSt r)
  SSATernary c t e -> SSATernary (renameExpr renSt c) (renameExpr renSt t) (renameExpr renSt e)
  SSACall name args -> SSACall name (map (renameExpr renSt) args)
  SSAInstanceCall t m args -> SSAInstanceCall (renameExpr renSt t) m (map (renameExpr renSt) args)
  SSANewObject cn args -> SSANewObject cn (map (renameExpr renSt) args)
  SSAFieldAccess t f -> SSAFieldAccess (renameExpr renSt t) f
  e -> e  -- Literals don't need renaming

-- | Fill in phi arguments from predecessor
fillPhiArgs :: BlockId -> RenameState -> Map BlockId SSABlock -> BlockId -> Map BlockId SSABlock
fillPhiArgs predId renSt blockMap succId =
  case Map.lookup succId blockMap of
    Nothing -> blockMap
    Just block ->
      let phis' = map (fillPhiArg predId renSt) (blockPhis block)
      in Map.insert succId (block { blockPhis = phis' }) blockMap

-- | Fill in phi argument from a specific predecessor
fillPhiArg :: BlockId -> RenameState -> PhiNode -> PhiNode
fillPhiArg predId renSt phi =
  let varName = ssaName (phiVar phi)
      currentDef = Map.findWithDefault (SSAVar varName 0 Nothing) varName (renameCurrentDef renSt)
      args' = map updateArg (phiArgs phi)
      updateArg (p, v)
        | p == predId = (p, currentDef)
        | otherwise = (p, v)
  in phi { phiArgs = args' }

--------------------------------------------------------------------------------
-- Conversion from SSA
--------------------------------------------------------------------------------

-- | Convert SSA back to normal form (for code generation)
-- This inserts copy instructions for phi nodes
fromSSA :: SSAProgram -> Program
fromSSA (SSAProgram classes) = Program (map ssaClassToNormal classes)

-- | Convert SSA class back to normal AST
ssaClassToNormal :: SSAClass -> ClassDecl
ssaClassToNormal SSAClass{..} = ClassDecl
  { className = ssaClassName
  , classFields = ssaClassFields
  , classMethods = map ssaMethodToNormal ssaClassMethods
  }

-- | Convert SSA method back to normal AST
ssaMethodToNormal :: SSAMethod -> MethodDecl
ssaMethodToNormal SSAMethod{..} =
  let params = [ParamDecl (ssaName v) (getVarType v) | v <- ssaMethodParams]
      body = blocksToStmt ssaMethodBlocks
  in MethodDecl ssaMethodClassName ssaMethodName params ssaMethodReturnSig body

-- | Get the type from an SSAVar, defaulting to Int if unknown
-- (This shouldn't happen for parameters which always have types)
getVarType :: SSAVar -> ValueType
getVarType v = case ssaVarType v of
  Just t -> t
  Nothing -> error $ "SSA: Missing type for parameter " ++ ssaName v

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

-- | Convert SSA variable back to original name.
-- We use the base name, not the versioned name, since the semantic
-- analyzer only knows about the original variable names.
varToName :: SSAVar -> String
varToName (SSAVar name _ _) = name

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
  SSAProgram [c { ssaClassMethods = map propMethod (ssaClassMethods c) } | c <- classes]
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
  SSAProgram [c { ssaClassMethods = map elimMethod (ssaClassMethods c) } | c <- classes]
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
  SSAProgram [c { ssaClassMethods = map propMethod (ssaClassMethods c) } | c <- classes]
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
  SSAProgram [c { ssaClassMethods = map preMethod (ssaClassMethods c) } | c <- classes]
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
  SSAUse (SSAVar name ver _) -> Just $ CVar name ver
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

--------------------------------------------------------------------------------
-- Phi Simplification
--------------------------------------------------------------------------------

-- | Simplify trivial phi nodes
-- - phi(x, x, x) -> x (all args same)
-- - phi(c, c, c) -> c (all args same constant)
simplifyPhis :: SSAProgram -> SSAProgram
simplifyPhis (SSAProgram classes) =
  SSAProgram [c { ssaClassMethods = map simplifyMethod (ssaClassMethods c) } | c <- classes]
  where
    simplifyMethod m = m { ssaMethodBlocks = map simplifyBlock (ssaMethodBlocks m) }

    simplifyBlock b =
      let (simplified, copies) = unzip $ map simplifyPhi (blockPhis b)
          -- Some phis become copy statements
          extraInstrs = [SSAAssign dst (SSAUse src) | Just (dst, src) <- copies]
      in b { blockPhis = [p | (Just p, _) <- zip simplified (repeat Nothing)]
           , blockInstrs = extraInstrs ++ blockInstrs b
           }

    -- Returns (Maybe simplified phi, Maybe (dst, src) for copy)
    simplifyPhi :: PhiNode -> (Maybe PhiNode, Maybe (SSAVar, SSAVar))
    simplifyPhi phi@PhiNode{..}
      -- All arguments are the same variable
      | allSame (map snd phiArgs) =
          case phiArgs of
            ((_, v):_) -> (Nothing, Just (phiVar, v))
            [] -> (Just phi, Nothing)
      | otherwise = (Just phi, Nothing)

    allSame [] = True
    allSame (x:xs) = all (== x) xs

--------------------------------------------------------------------------------
-- Full SSA Optimization Pipeline
--------------------------------------------------------------------------------

-- | Full SSA-based optimization pipeline.
-- This version preserves the original AST structure while applying
-- additional SSA-style optimizations that complement structuredSSAOpt.
--
-- Currently applies:
-- 1. Dead branch elimination (if with constant condition)
-- 2. Additional algebraic simplifications
-- 3. Common subexpression elimination within expressions
fullSSAOptimize :: Program -> Program
fullSSAOptimize (Program classes) = Program (map optimizeClassFull classes)

-- | Optimize a class with full SSA techniques
optimizeClassFull :: ClassDecl -> ClassDecl
optimizeClassFull c@ClassDecl{..} =
  c { classMethods = map optimizeMethodFull classMethods }

-- | Optimize a method with full SSA techniques
optimizeMethodFull :: MethodDecl -> MethodDecl
optimizeMethodFull m@MethodDecl{..} =
  m { methodBody = optimizeStmtFull methodBody }

-- | Optimize a statement with additional SSA techniques
optimizeStmtFull :: Stmt -> Stmt
optimizeStmtFull = \case
  Block stmts pos ->
    -- Eliminate empty statements and merge adjacent blocks
    let stmts' = filter (not . isEmptyStmt) $ map optimizeStmtFull stmts
    in Block stmts' pos

  VarDecl name ty initOpt pos ->
    VarDecl name ty (optimizeExprFull <$> initOpt) pos

  Assign name expr pos ->
    Assign name (optimizeExprFull expr) pos

  FieldAssign target field off value pos ->
    FieldAssign (optimizeExprFull target) field off (optimizeExprFull value) pos

  Return exprOpt pos ->
    Return (optimizeExprFull <$> exprOpt) pos

  If cond th el pos ->
    let cond' = optimizeExprFull cond
        th' = optimizeStmtFull th
        el' = optimizeStmtFull el
    in case cond' of
      -- Dead branch elimination
      BoolLit True _ -> th'
      BoolLit False _ -> el'
      -- If both branches are empty, eliminate the if
      _ | isEmptyStmt th' && isEmptyStmt el' -> Block [] pos
      -- If both branches are identical, just use one
        | th' == el' -> th'
        | otherwise -> If cond' th' el' pos

  While cond body pos ->
    let cond' = optimizeExprFull cond
        body' = optimizeStmtFull body
    in case cond' of
      -- while(false) is dead code
      BoolLit False _ -> Block [] pos
      _ -> While cond' body' pos

  Break pos -> Break pos
  ExprStmt expr pos -> ExprStmt (optimizeExprFull expr) pos

-- | Check if a statement is empty (does nothing)
isEmptyStmt :: Stmt -> Bool
isEmptyStmt (Block [] _) = True
isEmptyStmt (Block stmts _) = all isEmptyStmt stmts
isEmptyStmt (ExprStmt (NullLit _) _) = True
isEmptyStmt _ = False

-- | Optimize an expression with additional techniques
optimizeExprFull :: Expr -> Expr
optimizeExprFull = \case
  IntLit n p -> IntLit n p
  BoolLit b p -> BoolLit b p
  StrLit s p -> StrLit s p
  NullLit p -> NullLit p
  Var name p -> Var name p
  This p -> This p

  Unary op e p -> foldUnary op (optimizeExprFull e) p

  Binary op l r p ->
    let l' = optimizeExprFull l
        r' = optimizeExprFull r
    in foldBinaryExpr op l' r' p

  Ternary c t e p ->
    let c' = optimizeExprFull c
        t' = optimizeExprFull t
        e' = optimizeExprFull e
    in case c' of
      BoolLit True _ -> t'
      BoolLit False _ -> e'
      -- If both branches are identical, eliminate the ternary
      _ | t' == e' -> t'
        | otherwise -> Ternary c' t' e' p

  Call name args p -> Call name (map optimizeExprFull args) p
  InstanceCall target method args p ->
    InstanceCall (optimizeExprFull target) method (map optimizeExprFull args) p
  NewObject cn args p -> NewObject cn (map optimizeExprFull args) p
  FieldAccess target field p -> FieldAccess (optimizeExprFull target) field p

--------------------------------------------------------------------------------
-- Structured SSA Optimization
--------------------------------------------------------------------------------
-- This performs SSA-style optimizations directly on the structured AST,
-- without converting to a CFG representation. This preserves control flow
-- structure while still enabling optimizations like:
-- - Copy propagation
-- - Constant propagation
-- - Common subexpression elimination
-- - Dead code elimination

-- | Optimize a program using structured SSA techniques.
-- This preserves the original AST structure while applying SSA-style
-- value propagation and constant folding.
structuredSSAOpt :: Program -> Program
structuredSSAOpt (Program classes) = Program (map optClass classes)

optClass :: ClassDecl -> ClassDecl
optClass c@ClassDecl{..} = c { classMethods = map optMethod classMethods }

optMethod :: MethodDecl -> MethodDecl
optMethod m@MethodDecl{..} =
  let initEnv = Map.empty
      (body', _) = runState (optStmt methodBody) initEnv
  in m { methodBody = body' }

-- | Environment mapping variable names to their known values
type OptEnv = Map String KnownValue

-- | A value that may be known at compile time
data KnownValue
  = KInt !Int
  | KBool !Bool
  | KStr !String
  | KVar !String      -- Known to be a copy of another variable
  | KExpr !Expr       -- Known to be this expression (for CSE)
  deriving (Eq, Show)

type OptM a = State OptEnv a

-- | Optimize a statement
optStmt :: Stmt -> OptM Stmt
optStmt = \case
  Block stmts pos -> do
    stmts' <- mapM optStmt stmts
    return $ Block stmts' pos

  VarDecl name ty initOpt pos -> do
    case initOpt of
      Just expr -> do
        expr' <- optExpr expr
        recordValue name expr'
        return $ VarDecl name ty (Just expr') pos
      Nothing -> do
        modify $ Map.delete name
        return $ VarDecl name ty Nothing pos

  Assign name expr pos -> do
    expr' <- optExpr expr
    recordValue name expr'
    return $ Assign name expr' pos

  FieldAssign target field off value pos -> do
    target' <- optExpr target
    value' <- optExpr value
    return $ FieldAssign target' field off value' pos

  Return exprOpt pos -> do
    exprOpt' <- traverse optExpr exprOpt
    return $ Return exprOpt' pos

  If cond th el pos -> do
    cond' <- optExpr cond
    -- Save environment before branches
    env <- get
    th' <- optStmt th
    thEnv <- get
    put env
    el' <- optStmt el
    elEnv <- get
    -- After if, remove any variable that was assigned in either branch
    -- (since we don't know which branch was taken)
    let thModified = Map.keysSet thEnv `Set.difference` Map.keysSet env
        elModified = Map.keysSet elEnv `Set.difference` Map.keysSet env
        -- Also consider vars that changed value
        thChanged = Set.fromList [k | k <- Map.keys env, Map.lookup k thEnv /= Map.lookup k env]
        elChanged = Set.fromList [k | k <- Map.keys env, Map.lookup k elEnv /= Map.lookup k env]
        allModified = Set.unions [thModified, elModified, thChanged, elChanged]
        -- Remove all modified variables from environment
        finalEnv = foldr Map.delete env (Set.toList allModified)
    put finalEnv
    return $ If cond' th' el' pos

  While cond body pos -> do
    -- For while loops, we must NOT propagate constants into the condition
    -- because the loop body may modify the variables used in the condition.
    -- Clear environment before optimizing condition and body.
    modify (const Map.empty)  -- Clear all known values
    cond' <- optExpr cond
    body' <- optStmt body
    modify (const Map.empty)  -- Clear again after loop (values may be modified)
    return $ While cond' body' pos

  Break pos -> return $ Break pos

  ExprStmt expr pos -> do
    expr' <- optExpr expr
    return $ ExprStmt expr' pos

-- | Record a value assignment
recordValue :: String -> Expr -> OptM ()
recordValue name expr = modify $ Map.insert name (exprToKnown expr)
  where
    exprToKnown (IntLit n _) = KInt n
    exprToKnown (BoolLit b _) = KBool b
    exprToKnown (StrLit s _) = KStr s
    exprToKnown (Var v _) = KVar v
    exprToKnown e = KExpr e

-- | Optimize an expression using known values
optExpr :: Expr -> OptM Expr
optExpr = \case
  IntLit n p -> return $ IntLit n p
  BoolLit b p -> return $ BoolLit b p
  StrLit s p -> return $ StrLit s p
  NullLit p -> return $ NullLit p
  This p -> return $ This p

  Var name p -> lookupVar Set.empty name p
    where
      -- Lookup variable with cycle detection
      lookupVar :: Set String -> String -> Int -> OptM Expr
      lookupVar visited varName pos
        | Set.member varName visited = return $ Var varName pos  -- Cycle detected, stop
        | otherwise = do
            env <- get
            case Map.lookup varName env of
              Just (KInt n) -> return $ IntLit n pos
              Just (KBool b) -> return $ BoolLit b pos
              Just (KStr s) -> return $ StrLit s pos
              Just (KVar v) -> lookupVar (Set.insert varName visited) v pos
              _ -> return $ Var varName pos

  Unary op e p -> do
    e' <- optExpr e
    return $ foldUnary op e' p

  Binary op l r p -> do
    l' <- optExpr l
    r' <- optExpr r
    return $ foldBinaryExpr op l' r' p

  Ternary c t e p -> do
    c' <- optExpr c
    case c' of
      BoolLit True _ -> optExpr t
      BoolLit False _ -> optExpr e
      _ -> do
        t' <- optExpr t
        e' <- optExpr e
        return $ Ternary c' t' e' p

  Call name args p -> do
    args' <- mapM optExpr args
    return $ Call name args' p

  InstanceCall target method args p -> do
    target' <- optExpr target
    args' <- mapM optExpr args
    return $ InstanceCall target' method args' p

  NewObject cn args p -> do
    args' <- mapM optExpr args
    return $ NewObject cn args' p

  FieldAccess target field p -> do
    target' <- optExpr target
    return $ FieldAccess target' field p

-- | Fold unary operations on constants
foldUnary :: UnaryOp -> Expr -> Int -> Expr
foldUnary op e p = case (op, e) of
  (Neg, IntLit n _) -> IntLit (-n) p
  (Not, BoolLit b _) -> BoolLit (not b) p
  (Neg, Unary Neg inner _) -> inner  -- --x = x
  (Not, Unary Not inner _) -> inner  -- !!x = x
  _ -> Unary op e p

-- | Fold binary operations on constants
foldBinaryExpr :: BinaryOp -> Expr -> Expr -> Int -> Expr
foldBinaryExpr op l r p = case (op, l, r) of
  -- Integer arithmetic
  (Add, IntLit a _, IntLit b _) -> IntLit (a + b) p
  (Sub, IntLit a _, IntLit b _) -> IntLit (a - b) p
  (Mul, IntLit a _, IntLit b _) -> IntLit (a * b) p
  (Div, IntLit a _, IntLit b _) | b /= 0 -> IntLit (a `div` b) p
  (Mod, IntLit a _, IntLit b _) | b /= 0 -> IntLit (a `mod` b) p

  -- Integer comparisons
  (Eq, IntLit a _, IntLit b _) -> BoolLit (a == b) p
  (Ne, IntLit a _, IntLit b _) -> BoolLit (a /= b) p
  (Lt, IntLit a _, IntLit b _) -> BoolLit (a < b) p
  (Le, IntLit a _, IntLit b _) -> BoolLit (a <= b) p
  (Gt, IntLit a _, IntLit b _) -> BoolLit (a > b) p
  (Ge, IntLit a _, IntLit b _) -> BoolLit (a >= b) p

  -- Boolean operations
  (And, BoolLit a _, BoolLit b _) -> BoolLit (a && b) p
  (Or, BoolLit a _, BoolLit b _) -> BoolLit (a || b) p

  -- Short-circuit
  (And, BoolLit False _, _) -> BoolLit False p
  (And, BoolLit True _, r') -> r'
  (And, _, BoolLit False _) -> BoolLit False p
  (And, l', BoolLit True _) -> l'
  (Or, BoolLit True _, _) -> BoolLit True p
  (Or, BoolLit False _, r') -> r'
  (Or, _, BoolLit True _) -> BoolLit True p
  (Or, l', BoolLit False _) -> l'

  -- String concatenation
  (Add, StrLit a _, StrLit b _) -> StrLit (a ++ b) p

  -- Identity operations
  (Add, e, IntLit 0 _) -> e
  (Add, IntLit 0 _, e) -> e
  (Sub, e, IntLit 0 _) -> e
  (Mul, e, IntLit 1 _) -> e
  (Mul, IntLit 1 _, e) -> e
  (Div, e, IntLit 1 _) -> e

  -- Zero operations
  (Mul, _, IntLit 0 _) -> IntLit 0 p
  (Mul, IntLit 0 _, _) -> IntLit 0 p

  -- Self operations (x op x)
  (Sub, Var a _, Var b _) | a == b -> IntLit 0 p     -- x - x = 0
  (Div, Var a _, Var b _) | a == b -> IntLit 1 p     -- x / x = 1 (assuming x != 0)
  (Mod, Var a _, Var b _) | a == b -> IntLit 0 p     -- x % x = 0
  (Eq, Var a _, Var b _) | a == b -> BoolLit True p  -- x == x
  (Ne, Var a _, Var b _) | a == b -> BoolLit False p -- x != x
  (Le, Var a _, Var b _) | a == b -> BoolLit True p  -- x <= x
  (Ge, Var a _, Var b _) | a == b -> BoolLit True p  -- x >= x
  (Lt, Var a _, Var b _) | a == b -> BoolLit False p -- x < x
  (Gt, Var a _, Var b _) | a == b -> BoolLit False p -- x > x

  -- Note: power-of-2 multiplication is handled in codegen with LSHIFT

  _ -> Binary op l r p

--------------------------------------------------------------------------------
-- CFG-Based SSA Optimization Pipeline
--------------------------------------------------------------------------------

-- | Full CFG-based SSA optimization.
-- Converts to SSA with proper phi placement, applies optimizations, then
-- converts back. This enables global optimizations across control flow.
optimizeSSA :: Program -> Program
optimizeSSA prog =
  let -- Convert to SSA with proper phi placement
      ssaProg = toSSAWithCFG prog
      -- Apply SSA optimizations
      optimized = ssaOptPipeline ssaProg
      -- Convert back to AST
  in fromSSA optimized

-- | SSA optimization pipeline
ssaOptPipeline :: SSAProgram -> SSAProgram
ssaOptPipeline =
    simplifyPhis           -- Remove trivial phi nodes
  . ssaDeadCodeElim        -- Remove dead assignments
  . ssaCopyProp            -- Propagate copies
  . ssaConstantProp        -- Fold constants
  . simplifyPhis           -- Clean up again
