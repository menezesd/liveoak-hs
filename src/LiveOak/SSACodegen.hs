{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

-- | SSA-based code generation for LiveOak.
-- Generates SAM assembly directly from CFG/SSA form without lossy conversion.
module LiveOak.SSACodegen
  ( -- * Code Generation
    generateFromSSA
  , generateMethodFromCFG
  ) where

import Control.Monad (forM, forM_, unless)
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy as TL
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl')

import LiveOak.Ast (UnaryOp(..), BinaryOp(..))
import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Symbol (ProgramSymbols)
import LiveOak.Diag (Diag, Result)
import qualified LiveOak.Diag as D

--------------------------------------------------------------------------------
-- Code Generation Types
--------------------------------------------------------------------------------

-- | Code generation state
data SSACodegenState = SSACodegenState
  { scgLabelCounter :: !Int
  , scgCode :: !Builder
  , scgVarSlots :: !(Map String Int)  -- ^ Stack slot for each SSA variable
  , scgNextSlot :: !Int               -- ^ Next available stack slot
  }

-- | Code generation context
data SSACodegenCtx = SSACodegenCtx
  { scgSymbols :: !ProgramSymbols
  , scgClassName :: !String
  , scgMethodName :: !String
  , scgCFG :: !CFG
  , scgPhiCopies :: !(Map BlockId [(BlockId, String, String)])
    -- ^ For each block, copies to insert before jump: (target, destVar, srcVar)
  }

type SSACodegen a = ReaderT SSACodegenCtx (StateT SSACodegenState (Either Diag)) a

--------------------------------------------------------------------------------
-- Code Generation Entry Points
--------------------------------------------------------------------------------

-- | Generate SAM code from an SSA program
generateFromSSA :: SSAProgram -> ProgramSymbols -> Result Text
generateFromSSA (SSAProgram classes) syms = do
  codes <- forM classes $ \cls ->
    forM (ssaClassMethods cls) $ \method ->
      generateMethodSSA syms (ssaClassName cls) method
  return $ T.intercalate "\n" (concat codes)

-- | Generate SAM code for a single method from its CFG
generateMethodFromCFG :: ProgramSymbols -> String -> SSAMethod -> Result Text
generateMethodFromCFG = generateMethodSSA

--------------------------------------------------------------------------------
-- Method Code Generation
--------------------------------------------------------------------------------

-- | Generate code for a method using its CFG
generateMethodSSA :: ProgramSymbols -> String -> SSAMethod -> Result Text
generateMethodSSA syms clsName method@SSAMethod{..} = do
  let cfg = buildCFG method

      -- Compute phi copies to insert in predecessor blocks
      phiCopies = computePhiCopies cfg (ssaMethodBlocks)

      ctx = SSACodegenCtx
        { scgSymbols = syms
        , scgClassName = clsName
        , scgMethodName = ssaMethodName
        , scgCFG = cfg
        , scgPhiCopies = phiCopies
        }

      -- Allocate slots for parameters and local variables
      paramSlots = Map.fromList $ zip (map ssaName ssaMethodParams) [0..]
      nextSlot = length ssaMethodParams

      initState = SSACodegenState
        { scgLabelCounter = 0
        , scgCode = mempty
        , scgVarSlots = paramSlots
        , scgNextSlot = nextSlot
        }

  (_, finalState) <- runStateT (runReaderT (emitMethodCFG method) ctx) initState
  return $ TL.toStrict $ B.toLazyText $ scgCode finalState

-- | Emit a method using CFG
emitMethodCFG :: SSAMethod -> SSACodegen ()
emitMethodCFG SSAMethod{..} = do
  clsName <- asks scgClassName

  -- Emit method label
  let label = T.pack clsName <> "_" <> T.pack ssaMethodName
  emit $ "\n" <> label <> ":\n"

  -- Method prologue
  emit "LINK\n"

  -- Allocate space for local variables
  let allVars = collectAllVars ssaMethodBlocks
      paramNames = Set.fromList $ map ssaName ssaMethodParams
      localVars = Set.difference allVars paramNames
  unless (Set.null localVars) $
    emit $ "ADDSP " <> tshow (Set.size localVars) <> "\n"

  -- Allocate slots for local variables
  cfg <- asks scgCFG
  allocateVarSlots (Set.toList localVars)

  -- Emit blocks in reverse postorder
  let blockOrder = reversePostorder cfg
  forM_ blockOrder $ \blockId ->
    case getBlock cfg blockId of
      Just block -> emitBlock block
      Nothing -> return ()

  -- Method epilogue (return label)
  emit $ label <> "_return:\n"
  emit "UNLINK\n"
  emit "JUMPIND\n"

-- | Allocate stack slots for local variables
allocateVarSlots :: [String] -> SSACodegen ()
allocateVarSlots vars = do
  st <- get
  let startSlot = scgNextSlot st
      newSlots = Map.fromList $ zip vars [startSlot..]
      allSlots = Map.union (scgVarSlots st) newSlots
  put st { scgVarSlots = allSlots, scgNextSlot = startSlot + length vars }

-- | Collect all variable names from blocks
collectAllVars :: [SSABlock] -> Set.Set String
collectAllVars blocks = Set.unions $ map blockVars blocks
  where
    blockVars SSABlock{..} =
      Set.unions $ map phiVars blockPhis ++ map instrVars blockInstrs

    phiVars PhiNode{..} = Set.singleton (ssaName phiVar)

    instrVars (SSAAssign var _) = Set.singleton (ssaName var)
    instrVars _ = Set.empty

--------------------------------------------------------------------------------
-- Block Code Generation
--------------------------------------------------------------------------------

-- | Emit a single block
emitBlock :: CFGBlock -> SSACodegen ()
emitBlock CFGBlock{..} = do
  -- Emit block label
  emit $ T.pack cfgBlockId <> ":\n"

  -- Emit phi node copies (from predecessors that jump here)
  -- Note: actual phi copies are inserted in predecessor terminators
  -- Here we just need to load the correct value

  -- Emit instructions
  forM_ cfgInstrs emitInstr

  -- Emit terminator with phi copies
  emitTerminator cfgBlockId cfgTerm

-- | Emit an SSA instruction
emitInstr :: SSAInstr -> SSACodegen ()
emitInstr = \case
  SSAAssign var expr -> do
    emitSSAExpr expr
    slot <- getVarSlot (ssaName var)
    emit $ "STOREOFF " <> tshow slot <> "\n"

  SSAFieldStore target _field off value -> do
    emitSSAExpr target
    emit $ "PUSHIMM " <> tshow off <> "\n"
    emit "ADD\n"
    emitSSAExpr value
    emit "STOREIND\n"

  SSAReturn exprOpt -> do
    case exprOpt of
      Just expr -> emitSSAExpr expr
      Nothing -> emit "PUSHIMM 0\n"
    -- Store in return slot
    emit "STOREOFF -2\n"

  SSAJump _ -> return ()  -- Handled by terminator

  SSABranch _ _ _ -> return ()  -- Handled by terminator

  SSAExprStmt expr -> do
    emitSSAExpr expr
    emit "ADDSP -1\n"  -- Discard result

-- | Emit a block terminator
emitTerminator :: BlockId -> Terminator -> SSACodegen ()
emitTerminator currentBlock term = do
  -- Get phi copies to insert before this jump
  phiCopies <- asks scgPhiCopies
  let copies = Map.findWithDefault [] currentBlock phiCopies

  case term of
    TermJump target -> do
      -- Insert phi copies for the target block
      forM_ [(d, s) | (t, d, s) <- copies, t == target] $ \(dest, src) -> do
        srcSlot <- getVarSlot src
        destSlot <- getVarSlot dest
        emit $ "PUSHOFF " <> tshow srcSlot <> "\n"
        emit $ "STOREOFF " <> tshow destSlot <> "\n"
      emit $ "JUMP " <> T.pack target <> "\n"

    TermBranch cond thenBlock elseBlock -> do
      emitSSAExpr cond
      emit "ISNIL\n"
      emit $ "JUMPC " <> T.pack elseBlock <> "\n"
      -- Insert phi copies for then block
      forM_ [(d, s) | (t, d, s) <- copies, t == thenBlock] $ \(dest, src) -> do
        srcSlot <- getVarSlot src
        destSlot <- getVarSlot dest
        emit $ "PUSHOFF " <> tshow srcSlot <> "\n"
        emit $ "STOREOFF " <> tshow destSlot <> "\n"
      emit $ "JUMP " <> T.pack thenBlock <> "\n"

    TermReturn _ -> do
      clsName <- asks scgClassName
      methName <- asks scgMethodName
      let retLabel = T.pack clsName <> "_" <> T.pack methName <> "_return"
      emit $ "JUMP " <> retLabel <> "\n"

--------------------------------------------------------------------------------
-- Expression Code Generation
--------------------------------------------------------------------------------

-- | Emit an SSA expression
emitSSAExpr :: SSAExpr -> SSACodegen ()
emitSSAExpr = \case
  SSAInt n ->
    emit $ "PUSHIMM " <> tshow n <> "\n"

  SSABool b ->
    emit $ "PUSHIMM " <> (if b then "1" else "0") <> "\n"

  SSAStr s ->
    emit $ "PUSHIMMSTR \"" <> T.pack (escapeString s) <> "\"\n"

  SSANull ->
    emit "PUSHIMM 0\n"

  SSAUse var -> do
    slot <- getVarSlot (ssaName var)
    emit $ "PUSHOFF " <> tshow slot <> "\n"

  SSAThis -> do
    -- 'this' is the first parameter
    emit "PUSHOFF 0\n"

  SSAUnary op e -> do
    emitSSAExpr e
    case op of
      Neg -> do
        emit "PUSHIMM 0\n"
        emit "SWAP\n"
        emit "SUB\n"
      Not ->
        emit "ISNIL\n"

  SSABinary op l r -> do
    emitSSAExpr l
    emitSSAExpr r
    emitBinaryOp op

  SSATernary cond thenE elseE -> do
    elseLabel <- freshLabel "else"
    endLabel <- freshLabel "endif"
    emitSSAExpr cond
    emit "ISNIL\n"
    emit $ "JUMPC " <> elseLabel <> "\n"
    emitSSAExpr thenE
    emit $ "JUMP " <> endLabel <> "\n"
    emit $ elseLabel <> ":\n"
    emitSSAExpr elseE
    emit $ endLabel <> ":\n"

  SSACall name args -> do
    -- Push return slot
    emit "PUSHIMM 0\n"
    -- Push arguments
    forM_ args emitSSAExpr
    -- Call
    emit "LINK\n"
    -- TODO: proper label resolution
    emit $ "JSR " <> T.pack name <> "\n"
    emit "UNLINK\n"
    emit $ "ADDSP " <> tshow (negate $ length args) <> "\n"

  SSAInstanceCall target method args -> do
    emit "PUSHIMM 0\n"  -- Return slot
    emitSSAExpr target   -- Push 'this'
    forM_ args emitSSAExpr
    emit "LINK\n"
    -- TODO: proper label resolution based on target type
    emit $ "JSR " <> T.pack method <> "\n"
    emit "UNLINK\n"
    emit $ "ADDSP " <> tshow (negate $ length args + 1) <> "\n"

  SSANewObject _cn args -> do
    -- Allocate object
    emit $ "PUSHIMM " <> tshow (length args) <> "\n"
    emit "MALLOC\n"
    -- Initialize fields
    forM_ (zip [(0::Int)..] args) $ \(i, arg) -> do
      emit "DUP\n"
      emit $ "PUSHIMM " <> tshow i <> "\n"
      emit "ADD\n"
      emitSSAExpr arg
      emit "STOREIND\n"

  SSAFieldAccess target _field -> do
    -- TODO: need field offset lookup
    emitSSAExpr target
    emit "PUSHIMM 0\n"  -- Placeholder offset
    emit "ADD\n"
    emit "PUSHIND\n"

-- | Emit a binary operation
emitBinaryOp :: BinaryOp -> SSACodegen ()
emitBinaryOp = \case
  Add -> emit "ADD\n"
  Sub -> emit "SUB\n"
  Mul -> emit "TIMES\n"
  Div -> emit "DIV\n"
  Mod -> emit "MOD\n"
  Eq  -> emit "EQUAL\n"
  Ne  -> do emit "EQUAL\n"; emit "ISNIL\n"
  Lt  -> emit "LESS\n"
  Le  -> emit "LESSEQ\n"
  Gt  -> emit "GREATER\n"
  Ge  -> emit "GREATEREQ\n"
  And -> emit "AND\n"
  Or  -> emit "OR\n"
  Concat -> emit "ADD\n"  -- String concatenation uses ADD in SAM

--------------------------------------------------------------------------------
-- Phi Node Handling
--------------------------------------------------------------------------------

-- | Compute phi copies that need to be inserted in predecessor blocks
-- Returns: Map from source block -> [(target block, dest var, src var)]
computePhiCopies :: CFG -> [SSABlock] -> Map BlockId [(BlockId, String, String)]
computePhiCopies cfg blocks =
  let -- For each block with phi nodes, add copies to predecessors
      phiCopyList = concatMap (blockPhiCopies cfg) blocks
      -- Group by source block
  in foldl' addCopy Map.empty phiCopyList
  where
    addCopy m (srcBlock, targetBlock, destVar, srcVar) =
      Map.insertWith (++) srcBlock [(targetBlock, destVar, srcVar)] m

-- | Get phi copies for a block
blockPhiCopies :: CFG -> SSABlock -> [(BlockId, BlockId, String, String)]
blockPhiCopies _cfg SSABlock{..} =
  [ (predBlock, blockLabel, ssaName (phiVar phi), ssaName srcVar)
  | phi <- blockPhis
  , (predBlock, srcVar) <- phiArgs phi
  ]

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Emit code
emit :: Text -> SSACodegen ()
emit t = modify $ \s -> s { scgCode = scgCode s <> B.fromText t }

-- | Generate a fresh label
freshLabel :: Text -> SSACodegen Text
freshLabel prefix = do
  st <- get
  let n = scgLabelCounter st
  put st { scgLabelCounter = n + 1 }
  return $ prefix <> "_" <> T.pack (show n)

-- | Get stack slot for a variable
getVarSlot :: String -> SSACodegen Int
getVarSlot name = do
  slots <- gets scgVarSlots
  case Map.lookup name slots of
    Just slot -> return slot
    Nothing -> throwError $ D.ResolveError ("Unknown variable: " ++ name) 0 0

-- | Convert to text
tshow :: Show a => a -> Text
tshow = T.pack . show

-- | Escape a string for SAM
escapeString :: String -> String
escapeString = concatMap escape
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\t' = "\\t"
    escape c = [c]
