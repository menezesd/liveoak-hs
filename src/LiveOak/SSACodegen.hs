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

import Control.Monad (forM, forM_, when)
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
import Data.List (foldl', sort)
import Data.Maybe (isJust)

import LiveOak.Ast (UnaryOp(..), BinaryOp(..))
import LiveOak.SSATypes
import LiveOak.CFG
import LiveOak.Symbol (ProgramSymbols, lookupClass, csFieldOrder, lookupMethod, fieldOffset)
import LiveOak.Diag (Diag, Result)
import qualified LiveOak.Diag as D
import LiveOak.StringRuntime (emitStringRuntime)
import LiveOak.SSATypeInfer (TypeEnv, buildTypeEnv, inferSSAExprClass)

--------------------------------------------------------------------------------
-- Code Generation Types
--------------------------------------------------------------------------------

-- | Code generation state
data SSACodegenState = SSACodegenState
  { scgLabelCounter :: !Int
  , scgCode :: !Builder
  , scgVarSlots :: !(Map String Int)  -- ^ Stack slot for each SSA variable
  }

-- | Code generation context
data SSACodegenCtx = SSACodegenCtx
  { scgSymbols :: !ProgramSymbols
  , scgClassName :: !String
  , scgMethodName :: !String
  , scgCFG :: !CFG
  , scgPhiCopies :: !(Map BlockId [(BlockId, String, String)])
    -- ^ For each block, copies to insert before jump: (target, destVar, srcVar)
  , scgTypeEnv :: !TypeEnv
    -- ^ Type environment for inferring expression types
  , scgReturnSlotOffset :: !Int        -- ^ Offset of return slot relative to FBR
  , scgLocalCount :: !Int              -- ^ Number of locals to allocate
  }

type SSACodegen a = ReaderT SSACodegenCtx (StateT SSACodegenState (Either Diag)) a

--------------------------------------------------------------------------------
-- Code Generation Entry Points
--------------------------------------------------------------------------------

-- | Generate SAM code from an SSA program
generateFromSSA :: SSAProgram -> ProgramSymbols -> Result Text
generateFromSSA (SSAProgram classes) syms = do
  -- Generate preamble
  let preamble = generatePreamble syms

  -- Generate all methods
  codes <- forM classes $ \cls ->
    forM (ssaClassMethods cls) $ \method ->
      generateMethodSSA syms (ssaClassName cls) method

  -- Generate string runtime
  let stringRuntime = generateStringRuntime

  return $ T.intercalate "\n" [preamble, T.intercalate "\n" (concat codes), stringRuntime]

-- | Generate program preamble (allocate Main, call Main.main, STOP)
generatePreamble :: ProgramSymbols -> Text
generatePreamble syms =
  let mainFields = case lookupClass "Main" syms of
        Just cs -> length (csFieldOrder cs)
        Nothing -> 0
  in T.unlines
    [ "PUSHIMM " <> tshow mainFields
    , "MALLOC"
    , "PUSHIMM 0"
    , "SWAP"
    , "LINK"
    , "JSR Main_main"
    , "UNLINK"
    , "ADDSP -1"
    , "STOP"
    ]

-- | Generate string runtime functions
generateStringRuntime :: Text
generateStringRuntime = emitStringRuntime

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

      -- Build type environment for this method
      typeEnv = buildTypeEnv ssaMethodBlocks syms

      -- totalParams includes 'this' (like traditional codegen)
      totalParams = 1 + length ssaMethodParams
      returnSlotOffset = -(3 + totalParams)
      -- Parameters: this at index 0, user params follow
      paramSlots = Map.fromList $
        ("this", -(2 + totalParams) + 0) :
        zip (map ssaName ssaMethodParams) [-(2 + totalParams) + 1 + i | i <- [0..]]

      allVars = collectAllVars ssaMethodBlocks
      paramNames = Set.fromList $ "this" : map ssaName ssaMethodParams
      localVars = sort $ Set.toList $ Set.difference allVars paramNames
      localSlots = Map.fromList $ zip localVars [1..]

      varSlots = Map.union paramSlots localSlots
      localCount = length localVars

      ctx = SSACodegenCtx
        { scgSymbols = syms
        , scgClassName = clsName
        , scgMethodName = ssaMethodName
        , scgCFG = cfg
        , scgPhiCopies = phiCopies
        , scgTypeEnv = typeEnv
        , scgReturnSlotOffset = returnSlotOffset
        , scgLocalCount = localCount
        }

      initState = SSACodegenState
        { scgLabelCounter = 0
        , scgCode = mempty
        , scgVarSlots = varSlots
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
  localCount <- asks scgLocalCount
  when (localCount > 0) $
    emit $ "ADDSP " <> tshow localCount <> "\n"

  cfg <- asks scgCFG

  -- Emit blocks in reverse postorder
  let blockOrder = reversePostorder cfg
  forM_ blockOrder $ \blockId ->
    case getBlock cfg blockId of
      Just block -> emitBlock block
      Nothing -> return ()

  -- Method epilogue (return label)
  emit $ label <> "_return:\n"
  -- Pop local variables before unlinking (they're still on stack after ADDSP allocations)
  when (localCount > 0) $
    emit $ "ADDSP " <> tshow (-localCount) <> "\n"
  emit "UNLINK\n"
  emit "RST\n"

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
    -- Don't pop - leave value on stack (will be cleaned up at return)

  SSAFieldStore target _field off value -> do
    emitSSAExpr target
    emit $ "PUSHIMM " <> tshow off <> "\n"
    emit "ADD\n"
    emitSSAExpr value
    emit "STOREIND\n"

  SSAReturn exprOpt -> do
    returnSlot <- asks scgReturnSlotOffset
    case exprOpt of
      Just expr -> emitSSAExpr expr
      Nothing -> emit "PUSHIMM 0\n"
    -- Store in return slot (value stays on stack)
    emit $ "STOREOFF " <> tshow returnSlot <> "\n"

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

    TermReturn exprOpt -> do
      returnSlot <- asks scgReturnSlotOffset
      case exprOpt of
        Just expr -> emitSSAExpr expr
        Nothing -> emit "PUSHIMM 0\n"
      emit $ "STOREOFF " <> tshow returnSlot <> "\n"
      -- Don't pop - value stays on stack until return label pops locals
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
    slot <- getVarSlot "this"
    emit $ "PUSHOFF " <> tshow slot <> "\n"

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
    -- Push implicit 'this'
    thisSlot <- getVarSlot "this"
    emit $ "PUSHOFF " <> tshow thisSlot <> "\n"
    -- Push arguments
    forM_ args emitSSAExpr
    -- Call
    emit "LINK\n"
    clsName <- asks scgClassName
    syms <- asks scgSymbols
    let methodLabel = case lookupClass clsName syms >>= lookupMethod name of
          Just _ -> T.pack clsName <> "_" <> T.pack name
          Nothing -> T.pack name  -- Fallback
    emit $ "JSR " <> methodLabel <> "\n"
    emit "UNLINK\n"
    emit $ "ADDSP " <> tshow (negate $ length args + 1) <> "\n"  -- +1 for 'this', return slot stays

  SSAInstanceCall target method args -> do
    emit "PUSHIMM 0\n"  -- Return slot
    emitSSAExpr target   -- Push 'this'
    forM_ args emitSSAExpr
    emit "LINK\n"
    -- Infer target class type and use qualified method name
    syms <- asks scgSymbols
    typeEnv <- asks scgTypeEnv
    let methodLabel = case inferSSAExprClass syms typeEnv target of
          Just className -> T.pack className <> "_" <> T.pack method
          Nothing -> T.pack method  -- Fallback to bare name
    emit $ "JSR " <> methodLabel <> "\n"
    emit "UNLINK\n"
    emit $ "ADDSP " <> tshow (negate $ length args + 1) <> "\n"  -- +1 for 'this', return slot stays

  SSANewObject cn args -> do
    syms <- asks scgSymbols
    let nFields = case lookupClass cn syms of
          Just cs -> length (csFieldOrder cs)
          Nothing -> 1
        hasCtor = maybe False (isJust . lookupMethod cn) (lookupClass cn syms)
    -- Allocate object (heap initialized to 0)
    emit $ "PUSHIMM " <> tshow nFields <> "\n"
    emit "MALLOC\n"
    -- Call constructor if present
    when hasCtor $ do
      emit "DUP\n"       -- keep object for caller
      emit "PUSHIMM 0\n" -- return slot
      emit "SWAP\n"      -- place obj below return slot
      forM_ args emitSSAExpr
      let ctorLabel = T.pack cn <> "_" <> T.pack cn
          nArgs = length args + 1  -- +1 for 'this'
      emit "LINK\n"
      emit $ "JSR " <> ctorLabel <> "\n"
      emit "UNLINK\n"
      emit $ "ADDSP " <> tshow (negate nArgs) <> "\n"
      emit "ADDSP -1\n"  -- pop return slot

  SSAFieldAccess target field -> do
    -- Emit target expression
    emitSSAExpr target
    -- Infer target class and look up field offset
    syms <- asks scgSymbols
    typeEnv <- asks scgTypeEnv
    let offset = case inferSSAExprClass syms typeEnv target of
          Just className -> case lookupClass className syms of
            Just cs -> case fieldOffset field cs of
              Just off -> off
              Nothing -> 0  -- Field not found, use 0
            Nothing -> 0  -- Class not found, use 0
          Nothing -> 0  -- Can't infer type, use 0
    emit $ "PUSHIMM " <> tshow offset <> "\n"
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
