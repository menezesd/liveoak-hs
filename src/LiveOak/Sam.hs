{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | SAM (Stack Abstract Machine) simulator.
-- Executes SAM assembly code and returns the result.
module LiveOak.Sam
  ( -- * Types
    SamValue(..)
  , SamError(..)

    -- * Execution
  , runSam
  , runSamText
  , runSamDebug
  ) where

import Control.Monad (when)
import Data.Char (ord)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.List (foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector (Vector, (!?))
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | SAM values.
data SamValue
  = SamInt !Int
  deriving (Eq, Show)

-- | SAM errors.
data SamError
  = ParseError String
  | StackUnderflow String
  | DivisionByZero
  | InvalidMemoryAccess Int
  | UnknownLabel String
  | PCOutOfBounds Int
  | RuntimeError String
  deriving (Eq, Show)

-- | SAM instruction.
data SamInstr
  = PUSHIMM !Int
  | PUSHIMMSTR !String
  | DUP
  | SWAP
  | ADDSP !Int
  | ADD | SUB | TIMES | DIV | MOD
  | EQUAL | LESS | GREATER | CMP
  | ISNIL | ISNEG | ISPOS
  | AND | OR | NOT
  | PUSHOFF !Int
  | STOREOFF !Int
  | PUSHIND
  | STOREIND
  | MALLOC
  | JUMP !String
  | JUMPC !String
  | LINK
  | UNLINK
  | JSR !String
  | RST
  | STOP
  | NOP  -- For labels and comments
  deriving (Eq, Show)

-- | VM State.
data SamState = SamState
  { samStack   :: !(Vector SamValue)  -- Stack memory (fixed size, access by index)
  , samHeap    :: !(IntMap SamValue)  -- Heap memory
  , samPC      :: !Int                -- Program counter
  , samSP      :: !Int                -- Stack pointer (next free slot)
  , samFBR     :: !Int                -- Frame base register
  , samLabels  :: !(Map String Int)   -- Label -> instruction index
  , samCode    :: !(Vector SamInstr)  -- Program instructions
  , samHeapPtr :: !Int                -- Next free heap address
  }

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

-- | Parse SAM assembly code.
parseSam :: Text -> Either SamError (Vector SamInstr, Map String Int)
parseSam code = do
  let ls = map T.strip $ T.lines code
  (instrs, labels) <- parseLines ls 0 [] M.empty
  return (V.fromList $ reverse instrs, labels)

-- | Parse lines of SAM assembly.
parseLines :: [Text] -> Int -> [SamInstr] -> Map String Int
           -> Either SamError ([SamInstr], Map String Int)
parseLines [] _ instrs labels = Right (instrs, labels)
parseLines (line:rest) idx instrs labels = do
  let stripped = T.strip $ stripComment line
  if T.null stripped
    then parseLines rest idx instrs labels
    else if ":" `T.isSuffixOf` stripped
      then do
        -- It's a label
        let labelName = T.unpack $ T.dropWhileEnd (== ':') stripped
        parseLines rest idx instrs (M.insert labelName idx labels)
      else do
        -- It's an instruction
        instr <- parseInstr stripped
        parseLines rest (idx + 1) (instr : instrs) labels

-- | Strip comment from a line.
stripComment :: Text -> Text
stripComment t = case T.breakOn "//" t of
  (before, _) -> before

-- | Parse a single instruction.
parseInstr :: Text -> Either SamError SamInstr
parseInstr line = do
  let ws = T.words line
  case ws of
    [] -> Right NOP
    (op:args) -> parseOp (T.toUpper op) args

-- | Parse an operation with arguments.
parseOp :: Text -> [Text] -> Either SamError SamInstr
parseOp op args = case op of
  "PUSHIMM" -> case args of
    [n] -> case readInt n of
      Just i  -> Right $ PUSHIMM i
      Nothing -> Left $ ParseError $ "Invalid integer: " ++ T.unpack n
    _ -> Left $ ParseError "PUSHIMM requires one argument"

  "PUSHIMMSTR" -> do
    -- Reconstruct the string (may contain spaces)
    let argStr = T.unwords args
    case parseQuotedString argStr of
      Just s  -> Right $ PUSHIMMSTR s
      Nothing -> Left $ ParseError $ "Invalid string: " ++ T.unpack argStr

  "DUP"     -> Right DUP
  "SWAP"    -> Right SWAP

  "ADDSP" -> case args of
    [n] -> case readInt n of
      Just i  -> Right $ ADDSP i
      Nothing -> Left $ ParseError $ "Invalid integer: " ++ T.unpack n
    _ -> Left $ ParseError "ADDSP requires one argument"

  "ADD"     -> Right ADD
  "SUB"     -> Right SUB
  "TIMES"   -> Right TIMES
  "DIV"     -> Right DIV
  "MOD"     -> Right MOD
  "EQUAL"   -> Right EQUAL
  "LESS"    -> Right LESS
  "GREATER" -> Right GREATER
  "CMP"     -> Right CMP
  "ISNIL"   -> Right ISNIL
  "ISNEG"   -> Right ISNEG
  "ISPOS"   -> Right ISPOS
  "AND"     -> Right AND
  "OR"      -> Right OR
  "NOT"     -> Right NOT

  "PUSHOFF" -> case args of
    [n] -> case readInt n of
      Just i  -> Right $ PUSHOFF i
      Nothing -> Left $ ParseError $ "Invalid integer: " ++ T.unpack n
    _ -> Left $ ParseError "PUSHOFF requires one argument"

  "STOREOFF" -> case args of
    [n] -> case readInt n of
      Just i  -> Right $ STOREOFF i
      Nothing -> Left $ ParseError $ "Invalid integer: " ++ T.unpack n
    _ -> Left $ ParseError "STOREOFF requires one argument"

  "PUSHIND"  -> Right PUSHIND
  "STOREIND" -> Right STOREIND
  "MALLOC"   -> Right MALLOC

  "JUMP" -> case args of
    [lbl] -> Right $ JUMP (T.unpack lbl)
    _ -> Left $ ParseError "JUMP requires one argument"

  "JUMPC" -> case args of
    [lbl] -> Right $ JUMPC (T.unpack lbl)
    _ -> Left $ ParseError "JUMPC requires one argument"

  "LINK"   -> Right LINK
  "UNLINK" -> Right UNLINK

  "JSR" -> case args of
    [lbl] -> Right $ JSR (T.unpack lbl)
    _ -> Left $ ParseError "JSR requires one argument"

  "RST"  -> Right RST
  "STOP" -> Right STOP

  _ -> Left $ ParseError $ "Unknown instruction: " ++ T.unpack op

-- | Read an integer from text.
readInt :: Text -> Maybe Int
readInt t = case reads (T.unpack t) of
  [(n, "")] -> Just n
  _         -> Nothing

-- | Parse a quoted string, handling escape sequences.
parseQuotedString :: Text -> Maybe String
parseQuotedString t = do
  let s = T.unpack $ T.strip t
  case s of
    ('"':rest) -> case break (== '"') rest of
      (content, "\"") -> Just $ unescapeString content
      (content, '"':_) -> Just $ unescapeString content
      _ -> Nothing
    _ -> Nothing

-- | Unescape a string.
unescapeString :: String -> String
unescapeString [] = []
unescapeString ('\\':'n':rest) = '\n' : unescapeString rest
unescapeString ('\\':'t':rest) = '\t' : unescapeString rest
unescapeString ('\\':'r':rest) = '\r' : unescapeString rest
unescapeString ('\\':'"':rest) = '"' : unescapeString rest
unescapeString ('\\':'\\':rest) = '\\' : unescapeString rest
unescapeString (c:rest) = c : unescapeString rest

--------------------------------------------------------------------------------
-- Execution
--------------------------------------------------------------------------------

-- | Initial stack size.
stackSize :: Int
stackSize = 65536

-- | Initialize VM state.
initState :: Vector SamInstr -> Map String Int -> SamState
initState code labels = SamState
  { samStack   = V.replicate stackSize (SamInt 0)
  , samHeap    = IM.empty
  , samPC      = 0
  , samSP      = 0
  , samFBR     = 0
  , samLabels  = labels
  , samCode    = code
  , samHeapPtr = 1  -- Start at 1 to reserve 0 as null
  }

-- | Run SAM assembly and return result.
runSam :: String -> Either SamError SamValue
runSam = runSamText . T.pack

-- | Run SAM assembly from Text.
runSamText :: Text -> Either SamError SamValue
runSamText code = do
  (instrs, labels) <- parseSam code
  let st0 = initState instrs labels
  execLoopLimited 0 st0

-- | Maximum number of execution steps (prevents infinite loops).
maxSteps :: Int
maxSteps = 1000000

-- | Execution loop with step limit.
execLoopLimited :: Int -> SamState -> Either SamError SamValue
execLoopLimited steps st
  | steps > maxSteps = Left $ RuntimeError $ "Exceeded " ++ show maxSteps ++ " steps (infinite loop?)"
  | otherwise = case samCode st !? samPC st of
      Nothing -> Left $ PCOutOfBounds (samPC st)
      Just STOP -> stackTop st
      Just NOP  -> execLoopLimited (steps + 1) st { samPC = samPC st + 1 }
      Just instr -> do
        st' <- execInstr instr st
        execLoopLimited (steps + 1) st'

-- | Run SAM with debug trace output.
runSamDebug :: Text -> IO (Either SamError SamValue)
runSamDebug code = case parseSam code of
  Left err -> return $ Left err
  Right (instrs, labels) -> do
    let st0 = initState instrs labels
    execLoopDebug 0 st0

-- | Debug execution loop with tracing.
execLoopDebug :: Int -> SamState -> IO (Either SamError SamValue)
execLoopDebug steps st
  | steps > 100000 = return $ Left $ RuntimeError "Exceeded 100000 steps"
  | otherwise = case samCode st !? samPC st of
      Nothing -> return $ Left $ PCOutOfBounds (samPC st)
      Just STOP -> return $ stackTop st
      Just NOP  -> execLoopDebug (steps + 1) st { samPC = samPC st + 1 }
      Just instr -> do
        -- Print trace every step (can filter to specific instructions)
        putStrLn $ show (samPC st) ++ ": " ++ show instr
                ++ " | SP=" ++ show (samSP st)
                ++ " FBR=" ++ show (samFBR st)
                ++ " Stack[" ++ show (max 0 (samSP st - 5)) ++ ".." ++ show (samSP st - 1) ++ "]="
                ++ show [samStack st !? i | i <- [max 0 (samSP st - 5) .. samSP st - 1]]
        case execInstr instr st of
          Left err -> return $ Left err
          Right st' -> execLoopDebug (steps + 1) st'

-- | Main execution loop.
execLoop :: SamState -> Either SamError SamValue
execLoop st = case samCode st !? samPC st of
  Nothing -> Left $ PCOutOfBounds (samPC st)
  Just STOP -> stackTop st
  Just NOP  -> execLoop st { samPC = samPC st + 1 }
  Just instr -> do
    st' <- execInstr instr st
    execLoop st'

-- | Get top of stack.
stackTop :: SamState -> Either SamError SamValue
stackTop st
  | samSP st <= 0 = Left $ StackUnderflow "stackTop: empty stack"
  | otherwise = case samStack st !? (samSP st - 1) of
      Nothing -> Left $ StackUnderflow "stackTop: invalid SP"
      Just v  -> Right v

-- | Push a value onto the stack.
push :: SamValue -> SamState -> SamState
push v st = st
  { samStack = samStack st V.// [(samSP st, v)]
  , samSP = samSP st + 1
  }

-- | Pop a value from the stack.
pop :: SamState -> Either SamError (SamValue, SamState)
pop st
  | samSP st <= 0 = Left $ StackUnderflow "pop: empty stack"
  | otherwise = do
      let sp' = samSP st - 1
      case samStack st !? sp' of
        Nothing -> Left $ StackUnderflow "pop: invalid SP"
        Just v  -> Right (v, st { samSP = sp' })

-- | Pop an integer from the stack.
popInt :: SamState -> Either SamError (Int, SamState)
popInt st = do
  (v, st') <- pop st
  case v of
    SamInt n -> Right (n, st')

-- | Execute a single instruction.
execInstr :: SamInstr -> SamState -> Either SamError SamState
execInstr instr st = case instr of
  PUSHIMM n -> Right $ push (SamInt n) st { samPC = samPC st + 1 }

  PUSHIMMSTR s -> do
    -- Allocate string on heap
    let addr = samHeapPtr st
        len = length s + 1  -- +1 for null terminator
        chars = map (SamInt . ord) s ++ [SamInt 0]
        heap' = foldl' (\h (i, c) -> IM.insert (addr + i) c h)
                       (samHeap st)
                       (zip [0..] chars)
    Right $ push (SamInt addr) st
      { samPC = samPC st + 1
      , samHeap = heap'
      , samHeapPtr = samHeapPtr st + len
      }

  DUP -> do
    (v, _) <- pop st
    Right $ push v (push v st { samSP = samSP st - 1 }) { samPC = samPC st + 1 }

  SWAP -> do
    (a, st1) <- pop st     -- a is top of stack
    (b, st2) <- pop st1    -- b is second
    -- Push a first (to b's old position), then b (to a's old position) = SWAP
    Right $ push b (push a st2) { samPC = samPC st + 1 }

  ADDSP n -> Right st { samSP = samSP st + n, samPC = samPC st + 1 }

  ADD -> binaryIntOp (+) st
  SUB -> binaryIntOp (-) st
  TIMES -> binaryIntOp (*) st

  DIV -> do
    (b, st1) <- popInt st
    (a, st2) <- popInt st1
    when (b == 0) $ Left DivisionByZero
    Right $ push (SamInt (a `div` b)) st2 { samPC = samPC st + 1 }

  MOD -> do
    (b, st1) <- popInt st
    (a, st2) <- popInt st1
    when (b == 0) $ Left DivisionByZero
    Right $ push (SamInt (a `mod` b)) st2 { samPC = samPC st + 1 }

  EQUAL -> comparisonOp (==) st
  LESS -> comparisonOp (<) st
  GREATER -> comparisonOp (>) st
  CMP -> do
    (b, st1) <- popInt st
    (a, st2) <- popInt st1
    let cmpRes = if a < b then -1 else if a > b then 1 else 0
    Right $ push (SamInt cmpRes) st2 { samPC = samPC st + 1 }

  ISNIL -> do
    (v, st') <- popInt st
    Right $ push (SamInt $ if v == 0 then 1 else 0) st' { samPC = samPC st + 1 }

  ISNEG -> do
    (v, st') <- popInt st
    Right $ push (SamInt $ if v < 0 then 1 else 0) st' { samPC = samPC st + 1 }

  ISPOS -> do
    (v, st') <- popInt st
    Right $ push (SamInt $ if v > 0 then 1 else 0) st' { samPC = samPC st + 1 }

  AND -> binaryIntOp (\a b -> if a /= 0 && b /= 0 then 1 else 0) st
  OR  -> binaryIntOp (\a b -> if a /= 0 || b /= 0 then 1 else 0) st
  NOT -> do
    (v, st') <- popInt st
    Right $ push (SamInt $ if v == 0 then 1 else 0) st' { samPC = samPC st + 1 }

  PUSHOFF n -> do
    let addr = samFBR st + n
    case samStack st !? addr of
      Nothing -> Left $ InvalidMemoryAccess addr
      Just v  -> Right $ push v st { samPC = samPC st + 1 }

  STOREOFF n -> do
    (v, st') <- pop st
    let addr = samFBR st + n
        stackLen = V.length (samStack st')
    if addr < 0 || addr >= stackLen
      then Left $ InvalidMemoryAccess addr
      else Right st'
        { samStack = samStack st' V.// [(addr, v)]
        , samPC = samPC st + 1
        }

  PUSHIND -> do
    (addr, st') <- popInt st
    case IM.lookup addr (samHeap st') of
      Nothing -> Right $ push (SamInt 0) st' { samPC = samPC st + 1 }  -- Uninitialized = 0
      Just v  -> Right $ push v st' { samPC = samPC st + 1 }

  STOREIND -> do
    (v, st1) <- pop st
    (addr, st2) <- popInt st1
    Right st2
      { samHeap = IM.insert addr v (samHeap st2)
      , samPC = samPC st + 1
      }

  MALLOC -> do
    (size, st') <- popInt st
    let addr = samHeapPtr st'
        -- Allocate at least 1 slot even if size is 0
        actualSize = max 1 size
    -- Initialize allocated memory to 0
    let heap' = foldl' (\h i -> IM.insert (addr + i) (SamInt 0) h)
                       (samHeap st')
                       [0 .. actualSize - 1]
    Right $ push (SamInt addr) st'
      { samHeap = heap'
      , samHeapPtr = samHeapPtr st' + actualSize
      , samPC = samPC st + 1
      }

  JUMP lbl -> case M.lookup lbl (samLabels st) of
    Nothing -> Left $ UnknownLabel lbl
    Just pc -> Right st { samPC = pc }

  JUMPC lbl -> do
    (cond, st') <- popInt st
    if cond /= 0
      then case M.lookup lbl (samLabels st) of
        Nothing -> Left $ UnknownLabel lbl
        Just pc -> Right st' { samPC = pc }
      else Right st' { samPC = samPC st + 1 }

  LINK -> do
    -- Push FBR, set FBR = SP (before the push, i.e., where we store old FBR)
    let oldSP = samSP st
        st' = push (SamInt $ samFBR st) st
    Right st' { samFBR = oldSP, samPC = samPC st + 1 }

  UNLINK -> do
    -- Pop into FBR
    (fbr, st') <- popInt st
    Right st' { samFBR = fbr, samPC = samPC st + 1 }

  JSR lbl -> do
    -- Push return address (PC + 1), jump to label
    let st' = push (SamInt $ samPC st + 1) st
    case M.lookup lbl (samLabels st) of
      Nothing -> Left $ UnknownLabel lbl
      Just pc -> Right st' { samPC = pc }

  RST -> do
    -- Pop PC (return address)
    (pc, st') <- popInt st
    Right st' { samPC = pc }

  STOP -> Right st  -- Handled in execLoop
  NOP -> Right st { samPC = samPC st + 1 }

-- | Binary integer operation helper.
binaryIntOp :: (Int -> Int -> Int) -> SamState -> Either SamError SamState
binaryIntOp f st = do
  (b, st1) <- popInt st
  (a, st2) <- popInt st1
  Right $ push (SamInt $ f a b) st2 { samPC = samPC st + 1 }

-- | Comparison operation helper.
comparisonOp :: (Int -> Int -> Bool) -> SamState -> Either SamError SamState
comparisonOp f st = do
  (b, st1) <- popInt st
  (a, st2) <- popInt st1
  Right $ push (SamInt $ if f a b then 1 else 0) st2 { samPC = samPC st + 1 }
