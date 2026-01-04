{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Sparse Conditional Constant Propagation (SCCP).
--
-- == Overview
-- SCCP combines constant propagation with reachability analysis to:
--
-- * Propagate constants through the program
-- * Eliminate unreachable code (dead branches)
-- * Simplify conditional jumps with known conditions
--
-- == Algorithm (Two-Worklist Approach)
--
-- SCCP uses a lattice with three levels:
--
-- @
--        Top (undefined/never executed)
--         |
--    Constant values
--         |
--      Bottom (overdefined/varying)
-- @
--
-- The algorithm maintains two worklists:
--
-- 1. __CFG Worklist__: Edges to be marked executable
-- 2. __SSA Worklist__: Variables whose uses need re-evaluation
--
-- @
-- while worklists not empty:
--   if CFG edge (u,v) in CFG worklist:
--     mark edge executable
--     if v not yet visited: evaluate block v
--     else: re-evaluate phi nodes in v for new edge
--   if variable x in SSA worklist:
--     re-evaluate all uses of x in executable blocks
-- @
--
-- == Key Properties
--
-- * Only evaluates reachable code (conditional branches with constant
--   conditions only add one successor edge)
-- * Reaches fixed point in O(instructions × lattice height) time
-- * Monotonic: values only move down the lattice (Top → Const → Bottom)
--
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
import LiveOak.SSAUtils (blockMapFromList)
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
  { sccpValues :: !(Map VarKey LatticeValue)  -- ^ Lattice value for each SSA variable
  , sccpExecBlocks :: !(Set BlockId)          -- ^ Executable blocks
  , sccpExecEdges :: !(Set (BlockId, BlockId)) -- ^ Executable edges
  , sccpSSAWorklist :: ![VarKey]              -- ^ SSA variable worklist
  , sccpCFGWorklist :: ![(BlockId, BlockId)]  -- ^ CFG edge worklist
  } deriving (Show)

-- | Initial SCCP state
-- Parameters are initialized to Bottom (unknown/varying values)
initSCCPState :: BlockId -> [VarKey] -> SCCPState
initSCCPState entry params = SCCPState
  { sccpValues = Map.fromList [(p, Bottom) | p <- params]
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
  { sccpConstValues :: !(Map VarKey LatticeValue)  -- ^ Constant values found
  , sccpReachableBlocks :: !(Set BlockId)          -- ^ Reachable blocks
  , sccpDeadBlocks :: ![BlockId]                   -- ^ Unreachable blocks
  } deriving (Show)

-- | Run SCCP on a method
-- Takes a list of parameter variable keys (version 0) to initialize as Bottom
runSCCP :: [VarKey] -> CFG -> [SSABlock] -> SCCPResult
runSCCP params cfg blocks =
  let entry = cfgEntry cfg
      blockMap = blockMapFromList blocks
      useMap = buildUseMap blocks
      finalState = execState (sccpLoop cfg blockMap useMap) (initSCCPState entry params)
      allBlocks = Set.fromList $ allBlockIds cfg
      reachable = sccpExecBlocks finalState
      dead = Set.toList $ Set.difference allBlocks reachable
  in SCCPResult
    { sccpConstValues = sccpValues finalState
    , sccpReachableBlocks = reachable
    , sccpDeadBlocks = dead
    }

-- | Maximum iterations for SCCP fixed-point computation.
-- Most programs converge within a few hundred iterations.
maxSCCPIterations :: Int
maxSCCPIterations = 10000

-- | Main SCCP loop - process worklists until empty or iteration limit
sccpLoop :: CFG -> Map BlockId SSABlock -> Map VarKey (Set BlockId) -> SCCP ()
sccpLoop cfg blockMap useMap = go maxSCCPIterations
  where
    go 0 = return ()  -- Max iterations reached
    go n = do
      -- Process CFG worklist
      cfgDone <- processCFGWorklist cfg blockMap
      -- Process SSA worklist
      ssaDone <- processSSAWorklist cfg blockMap useMap
      -- Continue until both worklists are empty
      unless (cfgDone && ssaDone) $ go (n - 1)

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
processSSAWorklist :: CFG -> Map BlockId SSABlock -> Map VarKey (Set BlockId) -> SCCP Bool
processSSAWorklist cfg blockMap useMap = do
  st <- get
  case sccpSSAWorklist st of
    [] -> return True  -- Done
    (var:rest) -> do
      put st { sccpSSAWorklist = rest }
      -- Re-evaluate uses of this variable
      evaluateUses cfg blockMap useMap var
      return False  -- Not done

-- | Evaluate a block for the first time
evaluateBlock :: CFG -> SSABlock -> SCCP ()
evaluateBlock cfg SSABlock{..} = do
  -- Evaluate phi nodes using only executable incoming edges
  forM_ blockPhis $ \phi -> do
    evaluatePhi blockLabel phi
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
        argVal <- getVarValue (varKey argVar)
        oldVal <- getVarValue (varKey $ phiVar phi)
        let newVal = meet oldVal argVal
        when (newVal /= oldVal) $ do
          setVarValue (varKey $ phiVar phi) newVal
      Nothing -> return ()

-- | Evaluate a phi node
evaluatePhi :: BlockId -> PhiNode -> SCCP ()
evaluatePhi blockId PhiNode{..} = do
  execEdges <- gets sccpExecEdges
  vals <- forM phiArgs $ \(pred, argVar) ->
    if Set.member (pred, blockId) execEdges
      then Just <$> getVarValue (varKey argVar)
      else return Nothing
  let result = foldl' meet Top [v | Just v <- vals]
  setVarValue (varKey phiVar) result

-- | Evaluate an instruction
evaluateInstr :: SSAInstr -> SCCP ()
evaluateInstr = \case
  SSAAssign var expr -> do
    val <- evaluateExpr expr
    setVarValue (varKey var) val
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

  SSAUse var -> getVarValue (varKey var)

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
evaluateUses :: CFG -> Map BlockId SSABlock -> Map VarKey (Set BlockId) -> VarKey -> SCCP ()
evaluateUses cfg blockMap useMap var = do
  case Map.lookup var useMap of
    Nothing -> return ()
    Just blocks -> do
      execBlocks <- gets sccpExecBlocks
      forM_ (Set.toList blocks) $ \bid ->
        case Map.lookup bid blockMap of
          Just block | Set.member (blockLabel block) execBlocks ->
            evaluateBlock cfg block
          _ -> return ()

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

buildUseMap :: [SSABlock] -> Map VarKey (Set BlockId)
buildUseMap blocks = foldl' addBlock Map.empty blocks
  where
    addBlock acc SSABlock{..} =
      let bid = blockLabel
          uses = phiUses blockPhis ++ concatMap instrUses blockInstrs
      in foldl' (addUse bid) acc uses

    addUse bid acc v = Map.insertWith Set.union v (Set.singleton bid) acc

    phiUses phis =
      [ varKey v
      | phi <- phis
      , (_, v) <- phiArgs phi
      ]

    instrUses = \case
      SSAAssign _ e -> exprUses e
      SSAReturn (Just e) -> exprUses e
      SSABranch c _ _ -> exprUses c
      SSAFieldStore t _ _ v -> exprUses t ++ exprUses v
      SSAExprStmt e -> exprUses e
      _ -> []

    exprUses = \case
      SSAUse v -> [varKey v]
      SSAUnary _ e -> exprUses e
      SSABinary _ l r -> exprUses l ++ exprUses r
      SSATernary c t e -> exprUses c ++ exprUses t ++ exprUses e
      SSACall _ args -> concatMap exprUses args
      SSAInstanceCall t _ args -> exprUses t ++ concatMap exprUses args
      SSANewObject _ args -> concatMap exprUses args
      SSAFieldAccess t _ -> exprUses t
      _ -> []

-- | Get the lattice value of a variable
getVarValue :: VarKey -> SCCP LatticeValue
getVarValue var = do
  vals <- gets sccpValues
  return $ Map.findWithDefault Top var vals

-- | Set the lattice value of a variable
-- Uses meet to ensure monotonicity: values can only move down the lattice
-- (Top -> Const -> Bottom), never up. This makes SCCP robust against SSA violations.
setVarValue :: VarKey -> LatticeValue -> SCCP ()
setVarValue var val = do
  oldVal <- getVarValue var
  let newVal = meet oldVal val  -- Ensure we only move down the lattice
  when (newVal /= oldVal) $ do
    modify $ \s -> s
      { sccpValues = Map.insert var newVal (sccpValues s)
      , sccpSSAWorklist = var : sccpSSAWorklist s
      }

-- | Add a CFG edge to the worklist
addCFGEdge :: BlockId -> BlockId -> SCCP ()
addCFGEdge from to = do
  modify $ \s -> s { sccpCFGWorklist = (from, to) : sccpCFGWorklist s }
