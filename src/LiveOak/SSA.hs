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
  , ssaDeadCodeElim
  , ssaCopyProp
  , simplifyPhis
  , inline
  , strengthReduce
  , tailCallOptimize
  , stackAllocate
  , ssaPeephole
  , ssaOptPipeline

    -- * CFG-Based Optimization Pipeline
  , optimizeSSA         -- ^ Full CFG-based SSA optimization (WARNING: broken for complex programs)
  , optimizeSSAProgram  -- ^ Optimize SSA program, return SSA (for use with SSACodegen)
  , ssaBasicPipeline    -- ^ Basic safe SSA optimizations
  ) where

import LiveOak.Ast
import LiveOak.Types (ValueType)
import LiveOak.Symbol (ProgramSymbols, lookupClass, lookupField, fieldOffset)
import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Dominance
import qualified LiveOak.GVN as GVN
import qualified LiveOak.LICM as LICM
import qualified LiveOak.SCCP as SCCP
import LiveOak.Loop (findLoops)
import qualified LiveOak.Inline as Inline
import qualified LiveOak.StrengthReduce as SR
import qualified LiveOak.TailCall as TCO
import qualified LiveOak.Escape as Escape
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State
import Data.List (foldl')
import qualified LiveOak.Coalesce as Coalesce

--------------------------------------------------------------------------------
-- Conversion to SSA
--------------------------------------------------------------------------------

-- | Convert a program to SSA form
toSSA :: ProgramSymbols -> Program -> SSAProgram
toSSA syms (Program classes) = SSAProgram
  [classToSSA syms c | c <- classes]

-- | Convert a class to SSA form
classToSSA :: ProgramSymbols -> ClassDecl -> SSAClass
classToSSA syms ClassDecl{..} = SSAClass
  { ssaClassName = className
  , ssaClassFields = classFields
  , ssaClassMethods = map (methodToSSA syms className) classMethods
  }

-- | State for SSA conversion
data SSAState = SSAState
  { nextVersion :: !(Map String Int)    -- ^ Next version for each variable
  , currentDefs :: !(Map String SSAVar) -- ^ Current definition of each variable
  , nextBlockId :: !Int                 -- ^ For generating unique block labels
  , ssaSymbols :: !ProgramSymbols       -- ^ Symbol table for resolving fields
  , ssaCurrentClass :: !String          -- ^ Current class name
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
methodToSSA :: ProgramSymbols -> String -> MethodDecl -> SSAMethod
methodToSSA syms clsName MethodDecl{..} =
  let initState = SSAState Map.empty Map.empty 0 syms clsName
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
    -- Check if 'name' is a field of the current class
    st <- get
    let syms = ssaSymbols st
        clsName = ssaCurrentClass st
    case lookupClass clsName syms of
      Just cs -> case lookupField name cs of
        Just _fv -> do
          -- It's a field - convert to field store
          let offset = case fieldOffset name cs of
                Just off -> off
                Nothing -> 0
          return [SSABlock label [] [SSAFieldStore SSAThis name offset ssaExpr]]
        Nothing -> do
          -- It's a local variable
          v <- defineVar name
          return [SSABlock label [] [SSAAssign v ssaExpr]]
      Nothing -> do
        -- Class not found - treat as local variable
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
-- When we hit a control-flow statement (if/while), we need to ensure remaining
-- statements are placed correctly after the control flow, not mixed into the entry block.
stmtsToInstrs :: [Stmt] -> SSAConv ([SSAInstr], [SSABlock])
stmtsToInstrs stmts = go stmts []
  where
    go [] instrs = return (reverse instrs, [])
    go (stmt:rest) instrs = do
      blocks <- stmtToBlocks "temp" stmt
      case blocks of
        [SSABlock _ [] newInstrs] ->
          -- Simple statement - accumulate instructions
          go rest (reverse newInstrs ++ instrs)
        _ -> do
          -- Control flow statement - stop accumulating, create continuation blocks
          if null rest
            then return (reverse instrs, blocks)
            else do
              -- Create a new block for remaining statements
              nextLabel <- freshBlock
              (nextInstrs, nextBlocks) <- go rest []
              let contBlock = SSABlock nextLabel [] nextInstrs : nextBlocks
              -- Link last block of control flow to continuation
              let linkedBlocks = addJumpToEnd blocks nextLabel
              return (reverse instrs, linkedBlocks ++ contBlock)

-- | Convert an expression to SSA
exprToSSA :: Expr -> SSAConv SSAExpr
exprToSSA = \case
  IntLit n _ -> return $ SSAInt n
  BoolLit b _ -> return $ SSABool b
  StrLit s _ -> return $ SSAStr s
  NullLit _ -> return SSANull
  Var name _ -> do
    -- Check if 'name' is a field of the current class
    st <- get
    let syms = ssaSymbols st
        clsName = ssaCurrentClass st
    case lookupClass clsName syms of
      Just cs -> case lookupField name cs of
        Just _fv ->
          -- It's a field - convert to field access
          return $ SSAFieldAccess SSAThis name
        Nothing ->
          -- It's a local variable
          SSAUse <$> useVar name
      Nothing ->
        -- Class not found - treat as local variable
        SSAUse <$> useVar name
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
toSSAWithCFG :: ProgramSymbols -> Program -> SSAProgram
toSSAWithCFG syms (Program classes) = SSAProgram
  [classToSSAWithCFG syms c | c <- classes]

-- | Convert a class using CFG-based SSA
classToSSAWithCFG :: ProgramSymbols -> ClassDecl -> SSAClass
classToSSAWithCFG syms ClassDecl{..} = SSAClass
  { ssaClassName = className
  , ssaClassFields = classFields
  , ssaClassMethods = map (methodToSSAWithCFG syms className) classMethods
  }

-- | Convert a method using CFG-based SSA with proper phi placement
methodToSSAWithCFG :: ProgramSymbols -> String -> MethodDecl -> SSAMethod
methodToSSAWithCFG syms clsName decl@MethodDecl{..} =
  -- Step 1: Convert to basic blocks (with simple SSA naming)
  let basicMethod = methodToSSA syms clsName decl
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
          -- Process children in a dominator tree
          -- Do NOT thread renaming state across siblings; each child starts
          -- from the current block's state to avoid leaking definitions.
          (_, blockMap3) = foldl' (processChild cfg domTree renSt2)
                                  (renSt2, blockMap2)
                                  (domChildren domTree blockId)
      in (renSt2, blockMap3)

-- | Process a child in the dominator tree
processChild :: CFG -> DomTree -> RenameState -> (RenameState, Map BlockId SSABlock) -> BlockId
            -> (RenameState, Map BlockId SSABlock)
processChild cfg domTree parentState (renSt, blockMap) childId =
  let (_, blockMap') = renameBlock cfg domTree childId parentState blockMap
  in (renSt, blockMap')

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
-- WARNING: This function is BROKEN for programs with complex control flow!
-- It flattens all basic blocks linearly, losing while loops, if/else structure.
-- The instrToStmt function converts SSAJump -> empty block and SSABranch -> empty if.
--
-- PROPER FIX: Use LiveOak.SSACodegen.generateFromSSA instead of converting back to AST.
-- That generates code directly from the CFG without needing control flow reconstruction.
--
-- ALTERNATIVE FIX: Implement proper control flow structuring algorithm to rebuild
-- loops and conditionals from the CFG (complex).
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
ssaMethodToNormal method@SSAMethod{..} =
  let params = [ParamDecl (ssaName v) (getVarType v) | v <- ssaMethodParams]
      -- Build CFG and DomTree for coalescing
      cfg = buildCFG method
      domTree = computeDominators cfg
      -- Apply coalescing to eliminate phi copies
      coalesceResult = Coalesce.coalescePhiCopies cfg domTree ssaMethodBlocks
      coalescedBlocks = Coalesce.applyCoalescing coalesceResult ssaMethodBlocks
      -- Convert coalesced blocks back to statements
      body = Block (concatMap blockToStmts coalescedBlocks) 0
  in MethodDecl ssaMethodClassName ssaMethodName params ssaMethodReturnSig body

-- | Get the type from an SSAVar, defaulting to Int if unknown
-- (This shouldn't happen for parameters which always have types)
getVarType :: SSAVar -> ValueType
getVarType v = case ssaVarType v of
  Just t -> t
  Nothing -> error $ "SSA: Missing type for parameter " ++ ssaName v

-- | Convert SSA blocks to a statement
-- After coalescing, phi nodes are effectively gone or handled as regular assignments.
-- This function now just concatenates instructions from all blocks.
blocksToStmt :: [SSABlock] -> [Stmt]
blocksToStmt blocks = concatMap blockToStmts blocks

-- | Convert a single block to statements
blockToStmts :: SSABlock -> [Stmt]
blockToStmts SSABlock{..} = map instrToStmt blockInstrs

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
-- GVN Wrapper
--------------------------------------------------------------------------------

gvn :: SSAProgram -> SSAProgram
gvn (SSAProgram classes) = SSAProgram (map gvnClass classes)

gvnClass :: SSAClass -> SSAClass
gvnClass c = c { ssaClassMethods = map gvnMethod (ssaClassMethods c) }

gvnMethod :: SSAMethod -> SSAMethod
gvnMethod method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      gvnResult = GVN.runGVN cfg domTree (ssaMethodBlocks method)
  in method { ssaMethodBlocks = GVN.gvnOptBlocks gvnResult }

--------------------------------------------------------------------------------
-- SCCP Wrapper
--------------------------------------------------------------------------------

sccp :: SSAProgram -> SSAProgram
sccp (SSAProgram classes) =
  SSAProgram [c { ssaClassMethods = map sccpMethod (ssaClassMethods c) } | c <- classes]

sccpMethod :: SSAMethod -> SSAMethod
sccpMethod method =
  let cfg = buildCFG method
      sccpResult = SCCP.runSCCP cfg (ssaMethodBlocks method)
      constMap = Map.mapMaybe SCCP.getConstant (SCCP.sccpConstValues sccpResult)
      blocks' = map (applyConstPropagation constMap) (ssaMethodBlocks method)
      liveBlocks = filter (\b -> Set.member (blockLabel b) (SCCP.sccpReachableBlocks sccpResult)) blocks'
  in method { ssaMethodBlocks = liveBlocks }

applyConstPropagation :: Map String SSAExpr -> SSABlock -> SSABlock
applyConstPropagation consts block =
  block { blockInstrs = map (sccpSubstInstr consts) (blockInstrs block) }

sccpSubstInstr :: Map String SSAExpr -> SSAInstr -> SSAInstr
sccpSubstInstr consts = \case
  SSAAssign v e -> SSAAssign v (sccpSubstExpr consts e)
  SSAFieldStore t f off val -> SSAFieldStore (sccpSubstExpr consts t) f off (sccpSubstExpr consts val)
  SSAReturn e -> SSAReturn (sccpSubstExpr consts <$> e)
  SSABranch c t f -> SSABranch (sccpSubstExpr consts c) t f
  SSAExprStmt e -> SSAExprStmt (sccpSubstExpr consts e)
  i -> i

sccpSubstExpr :: Map String SSAExpr -> SSAExpr -> SSAExpr
sccpSubstExpr consts = \case
  SSAUse v -> case Map.lookup (ssaName v) consts of
                Just replacement -> replacement
                Nothing -> SSAUse v
  SSAUnary op e -> SSAUnary op (sccpSubstExpr consts e)
  SSABinary op l r -> SSABinary op (sccpSubstExpr consts l) (sccpSubstExpr consts r)
  SSATernary c t e -> SSATernary (sccpSubstExpr consts c) (sccpSubstExpr consts t) (sccpSubstExpr consts e)
  SSACall n args -> SSACall n (map (sccpSubstExpr consts) args)
  SSAInstanceCall t m args -> SSAInstanceCall (sccpSubstExpr consts t) m (map (sccpSubstExpr consts) args)
  SSANewObject cn args -> SSANewObject cn (map (sccpSubstExpr consts) args)
  SSAFieldAccess t f -> SSAFieldAccess (sccpSubstExpr consts t) f
  e -> e

--------------------------------------------------------------------------------
-- LICM Wrapper
--------------------------------------------------------------------------------

licm :: SSAProgram -> SSAProgram
licm (SSAProgram classes) = SSAProgram (map licmClass classes)

licmClass :: SSAClass -> SSAClass
licmClass c = c { ssaClassMethods = map licmMethod (ssaClassMethods c) }

licmMethod :: SSAMethod -> SSAMethod
licmMethod method =
  let cfg = buildCFG method
      domTree = computeDominators cfg
      loops = findLoops cfg domTree
      licmResult = LICM.runLICM cfg domTree loops (ssaMethodBlocks method)
  in method { ssaMethodBlocks = LICM.licmOptBlocks licmResult }

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
      let (newPhis, copies) = foldl' processPhi ([], []) (blockPhis b)
          newInstrs = map (\(dst, src) -> SSAAssign dst (SSAUse src)) copies ++ blockInstrs b
      in b { blockPhis = newPhis, blockInstrs = newInstrs }

    processPhi (phis, copies) phi =
      let args = map snd (phiArgs phi)
      in if not (null args) && all (== head args) (tail args)
         then (phis, (phiVar phi, head args) : copies)
         else (phi : phis, copies)

--------------------------------------------------------------------------------
-- Inline Wrapper
--------------------------------------------------------------------------------

-- | Inline functions in the program
inline :: SSAProgram -> SSAProgram
inline prog = Inline.inlineOptProgram (Inline.inlineFunctions Inline.defaultHeuristics prog)

--------------------------------------------------------------------------------
-- Strength Reduction Wrapper
--------------------------------------------------------------------------------

-- | Apply strength reduction to the program
strengthReduce :: SSAProgram -> SSAProgram
strengthReduce (SSAProgram classes) = SSAProgram (map srClass classes)
  where
    srClass c = c { ssaClassMethods = map srMethod (ssaClassMethods c) }
    srMethod method =
      let cfg = buildCFG method
          domTree = computeDominators cfg
          loops = findLoops cfg domTree
          srResult = SR.reduceStrength cfg domTree loops (ssaMethodBlocks method)
      in method { ssaMethodBlocks = SR.srOptBlocks srResult }

--------------------------------------------------------------------------------
-- Tail Call Optimization Wrapper
--------------------------------------------------------------------------------

-- | Apply tail call optimization to the program
tailCallOptimize :: SSAProgram -> SSAProgram
tailCallOptimize (SSAProgram classes) = SSAProgram (map tcoClass classes)
  where
    tcoClass c = c { ssaClassMethods = map tcoMethod (ssaClassMethods c) }
    tcoMethod method =
      let className = ssaMethodClassName method
          methodName = ssaMethodName method
          tcoResult = TCO.optimizeTailCalls className methodName (ssaMethodBlocks method)
      in method { ssaMethodBlocks = TCO.tcoOptBlocks tcoResult }

--------------------------------------------------------------------------------
-- SSA Peephole Optimization
--------------------------------------------------------------------------------

-- | SSA-level peephole optimizations
ssaPeephole :: SSAProgram -> SSAProgram
ssaPeephole (SSAProgram classes) = SSAProgram (map peepholeClass classes)

peepholeClass :: SSAClass -> SSAClass
peepholeClass c = c { ssaClassMethods = map peepholeMethod (ssaClassMethods c) }

peepholeMethod :: SSAMethod -> SSAMethod
peepholeMethod method = method { ssaMethodBlocks = map peepholeBlock (ssaMethodBlocks method) }

peepholeBlock :: SSABlock -> SSABlock
peepholeBlock block = block { blockInstrs = map peepholeInstr (blockInstrs block) }

peepholeInstr :: SSAInstr -> SSAInstr
peepholeInstr (SSAAssign var expr) = SSAAssign var (peepholeExpr expr)
peepholeInstr (SSAReturn (Just expr)) = SSAReturn (Just (peepholeExpr expr))
peepholeInstr (SSABranch cond t f) = SSABranch (peepholeExpr cond) t f
peepholeInstr other = other

peepholeExpr :: SSAExpr -> SSAExpr
peepholeExpr = \case
  -- double negation
  SSAUnary Neg (SSAUnary Neg e) -> peepholeExpr e
  SSAUnary Not (SSAUnary Not e) -> peepholeExpr e
  -- arithmetic identities
  SSABinary Add e (SSAInt 0) -> peepholeExpr e
  SSABinary Add (SSAInt 0) e -> peepholeExpr e
  SSABinary Sub e (SSAInt 0) -> peepholeExpr e
  SSABinary Mul e (SSAInt 1) -> peepholeExpr e
  SSABinary Mul (SSAInt 1) e -> peepholeExpr e
  SSABinary Div e (SSAInt 1) -> peepholeExpr e
  -- arithmetic with zero
  SSABinary Mul _ (SSAInt 0) -> SSAInt 0
  SSABinary Mul (SSAInt 0) _ -> SSAInt 0
  -- recursively apply
  SSAUnary op e -> SSAUnary op (peepholeExpr e)
  SSABinary op l r -> SSABinary op (peepholeExpr l) (peepholeExpr r)
  SSATernary c t e -> SSATernary (peepholeExpr c) (peepholeExpr t) (peepholeExpr e)
  other -> other

--------------------------------------------------------------------------------
-- Stack Allocation Wrapper
--------------------------------------------------------------------------------

-- | Perform escape analysis and mark objects for stack allocation
stackAllocate :: SSAProgram -> SSAProgram
stackAllocate (SSAProgram classes) = SSAProgram (map saClass classes)
  where
    saClass c = c { ssaClassMethods = map saMethod (ssaClassMethods c) }
    saMethod method =
      let cfg = buildCFG method
          escapeResult = Escape.analyzeEscape cfg (ssaMethodBlocks method)
      in method { ssaMethodBlocks = Escape.stackAllocate escapeResult (ssaMethodBlocks method) }

--------------------------------------------------------------------------------
-- CFG-Based SSA Optimization Pipeline
--------------------------------------------------------------------------------

-- | Full CFG-based SSA optimization on SSA programs.
-- Takes an SSA program and applies optimizations, returning optimized SSA.
-- The caller can then decide to use SSACodegen or fromSSA.
optimizeSSAProgram :: SSAProgram -> SSAProgram
optimizeSSAProgram ssaProg =
  -- Run a very limited cleanup pipeline (just 2 iterations max)
  -- Disable expensive optimizations that may cause issues
  fixedPointWithLimit 2 ssaBasicPipeline ssaProg

-- | Basic SSA optimization pipeline (safe, fast optimizations only)
ssaBasicPipeline :: SSAProgram -> SSAProgram
ssaBasicPipeline =
    ssaDeadCodeElim
  . ssaCopyProp
  . simplifyPhis

-- | Full CFG-based SSA optimization.
-- Converts to SSA with proper phi placement, applies optimizations, then
-- converts back. NOTE: fromSSA loses control flow - this is broken for complex programs!
-- Use optimizeSSAProgram + SSACodegen instead.
optimizeSSA :: ProgramSymbols -> Program -> Program
optimizeSSA syms prog =
  let ssaProg = toSSA syms prog
      optimized = optimizeSSAProgram ssaProg
  in fromSSA optimized

-- | Apply an optimization pass until a fixed point is reached or max iterations exceeded.
fixedPoint :: Eq a => (a -> a) -> a -> a
fixedPoint f x = fixedPointWithLimit 10 f x

-- | Apply optimization with explicit iteration limit.
fixedPointWithLimit :: Eq a => Int -> (a -> a) -> a -> a
fixedPointWithLimit 0 _ x = x  -- Max iterations reached
fixedPointWithLimit n f x =
  let x' = f x
  in if x' == x then x else fixedPointWithLimit (n - 1) f x'

-- | The main pipeline of optimizations that can be run iteratively.
ssaCleanupPipeline :: SSAProgram -> SSAProgram
ssaCleanupPipeline =
    gvn
  . sccp
  . licm
  . ssaDeadCodeElim
  . ssaCopyProp
  . simplifyPhis
  . ssaPeephole

-- | SSA optimization pipeline (old, kept for reference)
ssaOptPipeline :: SSAProgram -> SSAProgram
ssaOptPipeline =
    inline
  . strengthReduce
  . tailCallOptimize
  . gvn
  . sccp
  . licm
  . ssaDeadCodeElim
  . ssaCopyProp
  . simplifyPhis
