{-# LANGUAGE LambdaCase #-}

-- | Abstract Syntax Tree for LiveOak.
-- Defines expressions, statements, and operators.
module LiveOak.Ast
  ( -- * Operators
    UnaryOp (..)
  , BinaryOp (..)

    -- * Expressions
  , Expr (..)
  , exprPos

    -- * Statements
  , Stmt (..)
  , stmtPos

    -- * High-Level AST Nodes
  , Program (..)
  , ClassDecl (..)
  , MethodDecl (..)
  , ParamDecl (..)

    -- * Return Signatures
  , ReturnSig (..)
  ) where

import LiveOak.Types (Type, ValueType)

-- | Unary operators.
data UnaryOp
  = Neg  -- ^ Numeric/string negation: ~x
  | Not  -- ^ Boolean negation: !x
  deriving (Eq, Ord, Show)

-- | Binary operators.
data BinaryOp
  -- Arithmetic
  = Add   -- ^ Addition: +
  | Sub   -- ^ Subtraction: -
  | Mul   -- ^ Multiplication: *
  | Div   -- ^ Division: /
  | Mod   -- ^ Modulo: %
  -- Logical
  | And   -- ^ Logical AND: &
  | Or    -- ^ Logical OR: |
  -- Comparison
  | Eq    -- ^ Equality: =
  | Ne    -- ^ Not equal (not directly supported in LO-3)
  | Lt    -- ^ Less than: <
  | Le    -- ^ Less or equal (not directly supported)
  | Gt    -- ^ Greater than: >
  | Ge    -- ^ Greater or equal (not directly supported)
  -- String
  | Concat  -- ^ String concatenation (internal)
  deriving (Eq, Ord, Show)

-- | Expressions with source position.
data Expr
  -- Literals
  = IntLit    !Int !Int                           -- ^ Integer literal (value, pos)
  | BoolLit   !Bool !Int                          -- ^ Boolean literal (value, pos)
  | StrLit    !String !Int                        -- ^ String literal (value, pos)
  | NullLit   !Int                                -- ^ Null literal (pos)
  -- Variables
  | Var       !String !Int                        -- ^ Variable reference (name, pos)
  | This      !Int                                -- ^ 'this' reference (pos)
  -- Operators
  | Unary     !UnaryOp !Expr !Int                 -- ^ Unary operation (op, expr, pos)
  | Binary    !BinaryOp !Expr !Expr !Int          -- ^ Binary operation (op, left, right, pos)
  | Ternary   !Expr !Expr !Expr !Int              -- ^ Ternary (cond, then, else, pos)
  -- Calls
  | Call          !String ![Expr] !Int            -- ^ Method call (method, args, pos)
  | InstanceCall  !Expr !String ![Expr] !Int      -- ^ Instance method call (target, method, args, pos)
  -- Object operations
  | NewObject     !String ![Expr] !Int            -- ^ Object instantiation (class, args, pos)
  | FieldAccess   !Expr !String !Int              -- ^ Field access (target, field, pos)
  deriving (Eq, Show)

-- | Extract source position from an expression.
exprPos :: Expr -> Int
exprPos = \case
  IntLit _ p          -> p
  BoolLit _ p         -> p
  StrLit _ p          -> p
  NullLit p           -> p
  Var _ p             -> p
  This p              -> p
  Unary _ _ p         -> p
  Binary _ _ _ p      -> p
  Ternary _ _ _ p     -> p
  Call _ _ p          -> p
  InstanceCall _ _ _ p -> p
  NewObject _ _ p     -> p
  FieldAccess _ _ p   -> p

-- | Statements with source position.
data Stmt
  = Assign      !String !Expr !Int                        -- ^ Variable assignment (name, value, pos)
  | FieldAssign !Expr !String !Int !Expr !Int             -- ^ Field assignment (target, field, offset, value, pos)
  | VarDecl     !String !(Maybe ValueType) !(Maybe Expr) !Int  -- ^ Variable declaration (name, type, init, pos)
  | Return      !(Maybe Expr) !Int                        -- ^ Return statement (value, pos)
  | If          !Expr !Stmt !Stmt !Int                    -- ^ If statement (cond, then, else, pos)
  | While       !Expr !Stmt !Int                          -- ^ While loop (cond, body, pos)
  | Block       ![Stmt] !Int                              -- ^ Block of statements (stmts, pos)
  | Break       !Int                                      -- ^ Break statement (pos)
  | ExprStmt    !Expr !Int                                -- ^ Expression statement (expr, pos)
  deriving (Eq, Show)

-- | Extract source position from a statement.
stmtPos :: Stmt -> Int
stmtPos = \case
  Assign _ _ p        -> p
  FieldAssign _ _ _ _ p -> p
  VarDecl _ _ _ p     -> p
  Return _ p          -> p
  If _ _ _ p          -> p
  While _ _ p         -> p
  Block _ p           -> p
  Break p             -> p
  ExprStmt _ p        -> p

-- | Return signature for methods.
data ReturnSig
  = Void                  -- ^ No return value
  | RetPrim !Type         -- ^ Returns a primitive type
  | RetObj  !String       -- ^ Returns an object of given class
  deriving (Eq, Show)

-- | Parameter declaration.
data ParamDecl = ParamDecl
  { paramName :: !String
  , paramType :: !ValueType
  } deriving (Eq, Show)

-- | Method declaration.
data MethodDecl = MethodDecl
  { methodClassName  :: !String       -- ^ Containing class name
  , methodName       :: !String       -- ^ Method name
  , methodParams     :: ![ParamDecl]  -- ^ Parameters (excluding implicit 'this')
  , methodReturnSig  :: !ReturnSig    -- ^ Return signature
  , methodBody       :: !Stmt         -- ^ Method body (typically a Block)
  } deriving (Eq, Show)

-- | Class declaration.
data ClassDecl = ClassDecl
  { className   :: !String              -- ^ Class name
  , classFields :: ![(String, ValueType)]  -- ^ Field declarations (name, type)
  , classMethods :: ![MethodDecl]       -- ^ Method declarations
  } deriving (Eq, Show)

-- | Program: a list of class declarations.
newtype Program = Program
  { programClasses :: [ClassDecl]
  } deriving (Eq, Show)
