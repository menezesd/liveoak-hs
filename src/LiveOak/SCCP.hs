{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Sparse Conditional Constant Propagation (SCCP).
-- A powerful optimization that combines constant propagation with
-- reachability analysis to eliminate dead code and propagate constants.
module LiveOak.SCCP
  ( -- * SCCP Optimization
    runSCCP
  , SCCPResult(..)

    -- * Lattice Values
  , LatticeValue(..)
  , isConstant
  , getConstant
  ) where

import LiveOak.CFG
import LiveOak.SSATypes
import LiveOak.Ast (BinaryOp(..), UnaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (foldl')
import Control.Monad (forM, forM_, when, unless)
import Control.Monad.State.Strict

--------------------------------------------------------------------------------
-- Lattice Values
--------------------------------------------------------------------------------

-- | Lattice value for SCCP
-- Top = undefined (never executed)
-- Constant = known constant value
-- Bottom = overdefined (multiple possible values)
data LatticeValue
  = Top                    -- ^ Undefined (not yet computed)
  | ConstInt !Int          -- ^ Known integer constant
  | ConstBool !Bool        -- ^ Known boolean constant
  | ConstNull              -- ^ Known null
  | Bottom                 -- ^ Overdefined (varying value)
  deriving (Eq, Show)

-- | Check if a lattice value is a constant
isConstant :: LatticeValue -> Bool
isConstant (ConstInt _) = True
isConstant (ConstBool _) = True
isConstant ConstNull = True
isConstant _ = False

-- | Get constant value as an expression (if constant)
getConstant :: LatticeValue -> Maybe SSAExpr
getConstant (ConstInt n) = Just $ SSAInt n
getConstant (ConstBool b) = Just $ SSABool b
getConstant ConstNull = Just SSANull
getConstant _ = Nothing

-- | Meet operation on the lattice
-- Top ⊓ x = x
-- x ⊓ Top = x
-- Bottom ⊓ x = Bottom
-- x ⊓ Bottom = Bottom
-- Const a ⊓ Const b = Const a (if a == b) else Bottom
meet :: LatticeValue -> LatticeValue -> LatticeValue
meet Top x = x
meet x Top = x
meet Bottom _ = Bottom
meet _ Bottom = Bottom
meet (ConstInt a) (ConstInt b) = if a == b then ConstInt a else Bottom
meet (ConstBool a) (ConstBool b) = if a == b then ConstBool a else Bottom
meet ConstNull ConstNull = ConstNull
meet _ _ = Bottom  -- Different types

--------------------------------------------------------------------------------
-- SCCP State
--------------------------------------------------------------------------------

-- | SCCP analysis state
data SCCPState = SCCPState
  { sccpValues :: !(Map String LatticeValue)  -- ^ Lattice value for each SSA variable
  , sccpExecBlocks :: !(Set BlockId)          -- ^ Executable blocks
  , sccpExecEdges :: !(Set (BlockId, BlockId)) -- ^ Executable edges
  , sccpSSAWorklist :: ![String]              -- ^ SSA variable worklist
  , sccpCFGWorklist :: ![(BlockId, BlockId)]  -- ^ CFG edge worklist
  } deriving (Show)

-- | Initial SCCP state
initSCCPState :: BlockId -> SCCPState
initSCCPState entry = SCCPState
  { sccpValues = Map.empty
  , sccpExecBlocks = Set.empty
  , sccpExecEdges = Set.empty
  , sccpSSAWorklist = []
  , sccpCFGWorklist = [("__entry__", entry)]  -- Virtual entry edge
  }

type SCCP a = State SCCPState a

--------------------------------------------------------------------------------
-- SCCP Algorithm
--------------------------------------------------------------------------------

-- | Result of SCCP analysis
data SCCPResult = SCCPResult
  { sccpConstValues :: !(Map String LatticeValue)  -- ^ Constant values found
  , sccpReachableBlocks :: !(Set BlockId)          -- ^ Reachable blocks
  , sccpDeadBlocks :: ![BlockId]                   -- ^ Unreachable blocks
  } deriving (Show)

-- | Run SCCP on a method
runSCCP :: CFG -> [SSABlock] -> SCCPResult
runSCCP cfg blocks =
  let entry = cfgEntry cfg
      blockMap = Map.fromList [(blockLabel b, b) | b <- blocks]
      finalState = execState (sccpLoop cfg blockMap) (initSCCPState entry)
      allBlocks = Set.fromList $ allBlockIds cfg
      reachable = sccpExecBlocks finalState
      dead = Set.toList $ Set.difference allBlocks reachable
  in SCCPResult
    { sccpConstValues = sccpValues finalState
    , sccpReachableBlocks = reachable
    , sccpDeadBlocks = dead
    }

-- | Main SCCP loop - process worklists until empty
sccpLoop :: CFG -> Map BlockId SSABlock -> SCCP ()
sccpLoop cfg blockMap = do
  -- Process CFG worklist
  cfgDone <- processCFGWorklist cfg blockMap
  -- Process SSA worklist
  ssaDone <- processSSAWorklist cfg blockMap
  -- Continue until both worklists are empty
  unless (cfgDone && ssaDone) $ sccpLoop cfg blockMap

-- | Process CFG edge worklist
processCFGWorklist :: CFG -> Map BlockId SSABlock -> SCCP Bool
processCFGWorklist cfg blockMap = do
  st <- get
  case sccpCFGWorklist st of
    [] -> return True  -- Done
    ((from, to):rest) -> do
      put st { sccpCFGWorklist = rest }
      execEdges <- gets sccpExecEdges
      unless (Set.member (from, to) execEdges) $ do
        -- Mark edge as executable
        modify $ \s -> s { sccpExecEdges = Set.insert (from, to) execEdges }
        execBlocks <- gets sccpExecBlocks
        if Set.member to execBlocks
          then do
            -- Block already executed - just evaluate phis for new edge
            case Map.lookup to blockMap of
              Just block -> evaluatePhisForEdge from block
              Nothing -> return ()
          else do
            -- First time executing this block
            modify $ \s -> s { sccpExecBlocks = Set.insert to execBlocks }
            case Map.lookup to blockMap of
              Just block -> evaluateBlock cfg block
              Nothing -> return ()
      return False  -- Not done

-- | Process SSA variable worklist
processSSAWorklist :: CFG -> Map BlockId SSABlock -> SCCP Bool
processSSAWorklist cfg blockMap = do
  st <- get
  case sccpSSAWorklist st of
    [] -> return True  -- Done
    (var:rest) -> do
      put st { sccpSSAWorklist = rest }
      -- Re-evaluate uses of this variable
      evaluateUses cfg blockMap var
      return False  -- Not done

-- | Evaluate a block for the first time
evaluateBlock :: CFG -> SSABlock -> SCCP ()
evaluateBlock cfg SSABlock{..} = do
  -- Evaluate phi nodes
  forM_ blockPhis $ \phi -> do
    evaluatePhi phi
  -- Evaluate instructions
  forM_ blockInstrs $ \instr -> do
    evaluateInstr instr
  -- Evaluate terminator
  evaluateTerminator cfg blockLabel blockInstrs

-- | Evaluate phi nodes when a new edge becomes executable
evaluatePhisForEdge :: BlockId -> SSABlock -> SCCP ()
evaluatePhisForEdge from SSABlock{..} = do
  forM_ blockPhis $ \phi -> do
    -- Only consider the argument from the new edge
    case lookup from (phiArgs phi) of
      Just argVar -> do
        argVal <- getVarValue (ssaName argVar)
        oldVal <- getVarValue (ssaName $ phiVar phi)
        let newVal = meet oldVal argVal
        when (newVal /= oldVal) $ do
          setVarValue (ssaName $ phiVar phi) newVal
      Nothing -> return ()

-- | Evaluate a phi node
evaluatePhi :: PhiNode -> SCCP ()
evaluatePhi PhiNode{..} = do
  -- Meet values from all phi arguments
  -- (simplified: we should only consider executable incoming edges)
  vals <- forM phiArgs $ \(_, argVar) -> getVarValue (ssaName argVar)
  let result = foldl' meet Top vals
  setVarValue (ssaName phiVar) result

-- | Evaluate an instruction
evaluateInstr :: SSAInstr -> SCCP ()
evaluateInstr = \case
  SSAAssign var expr -> do
    val <- evaluateExpr expr
    setVarValue (ssaName var) val
  _ -> return ()  -- Other instructions don't define values we track

-- | Evaluate the terminator to determine executable edges
evaluateTerminator :: CFG -> BlockId -> [SSAInstr] -> SCCP ()
evaluateTerminator _cfg blockId instrs = do
  case findTerminator instrs of
    Just (SSAJump target) ->
      addCFGEdge blockId target
    Just (SSABranch cond thenB elseB) -> do
      condVal <- evaluateExpr cond
      case condVal of
        ConstBool True -> addCFGEdge blockId thenB
        ConstBool False -> addCFGEdge blockId elseB
        ConstInt n -> if n /= 0
                      then addCFGEdge blockId thenB
                      else addCFGEdge blockId elseB
        ConstNull -> addCFGEdge blockId elseB  -- null is falsy
        _ -> do  -- Unknown - both branches possible
          addCFGEdge blockId thenB
          addCFGEdge blockId elseB
    Just (SSAReturn _) -> return ()  -- No successors
    Just _ -> return ()  -- Other instructions (not terminators)
    Nothing -> return ()
  where
    findTerminator [] = Nothing
    findTerminator [x] = Just x
    findTerminator (_:xs) = findTerminator xs

-- | Evaluate an expression to a lattice value
evaluateExpr :: SSAExpr -> SCCP LatticeValue
evaluateExpr = \case
  SSAInt n -> return $ ConstInt n
  SSABool b -> return $ ConstBool b
  SSANull -> return ConstNull
  SSAStr _ -> return Bottom  -- Strings not tracked
  SSAThis -> return Bottom   -- 'this' is unknown

  SSAUse var -> getVarValue (ssaName var)

  SSAUnary op e -> do
    val <- evaluateExpr e
    return $ evaluateUnary op val

  SSABinary op l r -> do
    lval <- evaluateExpr l
    rval <- evaluateExpr r
    return $ evaluateBinary op lval rval

  SSATernary cond thenE elseE -> do
    condVal <- evaluateExpr cond
    case condVal of
      ConstBool True -> evaluateExpr thenE
      ConstBool False -> evaluateExpr elseE
      ConstInt n -> if n /= 0 then evaluateExpr thenE else evaluateExpr elseE
      ConstNull -> evaluateExpr elseE
      Top -> return Top
      Bottom -> do
        thenVal <- evaluateExpr thenE
        elseVal <- evaluateExpr elseE
        return $ meet thenVal elseVal

  SSACall _ _ -> return Bottom  -- Calls are not constant
  SSAInstanceCall _ _ _ -> return Bottom
  SSANewObject _ _ -> return Bottom
  SSAFieldAccess _ _ -> return Bottom

-- | Evaluate a unary operation
evaluateUnary :: UnaryOp -> LatticeValue -> LatticeValue
evaluateUnary _ Top = Top
evaluateUnary _ Bottom = Bottom
evaluateUnary Neg (ConstInt n) = ConstInt (-n)
evaluateUnary Not (ConstBool b) = ConstBool (not b)
evaluateUnary Not (ConstInt n) = ConstBool (n == 0)
evaluateUnary Not ConstNull = ConstBool True
evaluateUnary _ _ = Bottom

-- | Evaluate a binary operation
evaluateBinary :: BinaryOp -> LatticeValue -> LatticeValue -> LatticeValue
evaluateBinary _ Top _ = Top
evaluateBinary _ _ Top = Top
evaluateBinary _ Bottom _ = Bottom
evaluateBinary _ _ Bottom = Bottom
evaluateBinary op (ConstInt l) (ConstInt r) = case op of
  Add -> ConstInt (l + r)
  Sub -> ConstInt (l - r)
  Mul -> ConstInt (l * r)
  Div -> if r == 0 then Bottom else ConstInt (l `div` r)
  Mod -> if r == 0 then Bottom else ConstInt (l `mod` r)
  Eq  -> ConstBool (l == r)
  Ne  -> ConstBool (l /= r)
  Lt  -> ConstBool (l < r)
  Le  -> ConstBool (l <= r)
  Gt  -> ConstBool (l > r)
  Ge  -> ConstBool (l >= r)
  And -> ConstBool (l /= 0 && r /= 0)
  Or  -> ConstBool (l /= 0 || r /= 0)
  Concat -> Bottom  -- Can't concat ints
evaluateBinary op (ConstBool l) (ConstBool r) = case op of
  And -> ConstBool (l && r)
  Or  -> ConstBool (l || r)
  Eq  -> ConstBool (l == r)
  Ne  -> ConstBool (l /= r)
  _ -> Bottom
evaluateBinary Eq ConstNull ConstNull = ConstBool True
evaluateBinary Ne ConstNull ConstNull = ConstBool False
evaluateBinary _ _ _ = Bottom

-- | Re-evaluate all uses of a variable
evaluateUses :: CFG -> Map BlockId SSABlock -> String -> SCCP ()
evaluateUses _cfg blockMap var = do
  -- Find all blocks that use this variable and re-evaluate
  forM_ (Map.elems blockMap) $ \block -> do
    execBlocks <- gets sccpExecBlocks
    when (Set.member (blockLabel block) execBlocks) $ do
      -- Check if block uses this variable
      when (usesVar var block) $ do
        evaluateBlock' block
  where
    usesVar v SSABlock{..} =
      any (usesVarInPhi v) blockPhis || any (usesVarInInstr v) blockInstrs

    usesVarInPhi v PhiNode{..} =
      any (\(_, argVar) -> ssaName argVar == v) phiArgs

    usesVarInInstr v = \case
      SSAAssign _ expr -> usesVarInExpr v expr
      SSAReturn (Just expr) -> usesVarInExpr v expr
      SSABranch cond _ _ -> usesVarInExpr v cond
      SSAFieldStore target _ _ value ->
        usesVarInExpr v target || usesVarInExpr v value
      SSAExprStmt expr -> usesVarInExpr v expr
      _ -> False

    usesVarInExpr v = \case
      SSAUse var' -> ssaName var' == v
      SSAUnary _ e -> usesVarInExpr v e
      SSABinary _ l r -> usesVarInExpr v l || usesVarInExpr v r
      SSATernary c t e -> usesVarInExpr v c || usesVarInExpr v t || usesVarInExpr v e
      SSACall _ args -> any (usesVarInExpr v) args
      SSAInstanceCall target _ args ->
        usesVarInExpr v target || any (usesVarInExpr v) args
      SSANewObject _ args -> any (usesVarInExpr v) args
      SSAFieldAccess target _ -> usesVarInExpr v target
      _ -> False

-- | Re-evaluate a block (just instructions, not phis)
evaluateBlock' :: SSABlock -> SCCP ()
evaluateBlock' SSABlock{..} = do
  forM_ blockInstrs evaluateInstr

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Get the lattice value of a variable
getVarValue :: String -> SCCP LatticeValue
getVarValue var = do
  vals <- gets sccpValues
  return $ Map.findWithDefault Top var vals

-- | Set the lattice value of a variable
setVarValue :: String -> LatticeValue -> SCCP ()
setVarValue var val = do
  oldVal <- getVarValue var
  when (val /= oldVal) $ do
    modify $ \s -> s
      { sccpValues = Map.insert var val (sccpValues s)
      , sccpSSAWorklist = var : sccpSSAWorklist s
      }

-- | Add a CFG edge to the worklist
addCFGEdge :: BlockId -> BlockId -> SCCP ()
addCFGEdge from to = do
  modify $ \s -> s { sccpCFGWorklist = (from, to) : sccpCFGWorklist s }
