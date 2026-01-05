{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | SSA Optimizations.
-- Core optimization passes that operate on SSA form.
--
module LiveOak.SSAOptimize
  ( -- * Optimizations
    ssaDeadCodeElim
  , ssaCopyProp
  , simplifyPhis
  , ssaPeephole

    -- * Helpers
  , exprEqual
  ) where

import LiveOak.SSATypes
import LiveOak.SSAUtils (substVarsInInstr)
import LiveOak.Ast (UnaryOp(..), BinaryOp(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Dead Code Elimination
--------------------------------------------------------------------------------

-- | Dead code elimination on SSA
ssaDeadCodeElim :: SSAProgram -> SSAProgram
ssaDeadCodeElim (SSAProgram classes) =
  SSAProgram [c { ssaClassMethods = map elimMethod (ssaClassMethods c) } | c <- classes]
  where
    elimMethod m =
      let blocks = ssaMethodBlocks m
          defMap = buildDefMap blocks
          live = propagateLive defMap (collectEssential blocks)
          blocks' = map (elimBlock live) blocks
      in m { ssaMethodBlocks = blocks' }

    elimBlock live b = b
      { blockPhis = filter (isLive live . phiVar) (blockPhis b)
      , blockInstrs = filter (instrIsLive live) (blockInstrs b)
      }

    isLive live v = Set.member (varKey v) live

    instrIsLive _ (SSAReturn _) = True
    instrIsLive _ (SSAJump _) = True
    instrIsLive _ (SSABranch _ _ _) = True
    instrIsLive _ (SSAFieldStore _ _ _ _) = True
    instrIsLive _ (SSAExprStmt _) = True
    instrIsLive live (SSAAssign v e) = isLive live v || hasSideEffects e

    -- | Check if expression has side effects (method calls, object creation)
    hasSideEffects :: SSAExpr -> Bool
    hasSideEffects = \case
      SSACall _ _ -> True          -- Method call on self
      SSAInstanceCall _ _ _ -> True  -- Method call on instance
      SSANewObject _ _ -> True      -- Constructor call
      SSAUnary _ e -> hasSideEffects e
      SSABinary _ l r -> hasSideEffects l || hasSideEffects r
      SSATernary c t e -> hasSideEffects c || hasSideEffects t || hasSideEffects e
      SSAFieldAccess t _ -> hasSideEffects t
      _ -> False

    collectEssential blocks =
      Set.unions (map blockEssential blocks)
      where
        blockEssential SSABlock{..} =
          Set.unions (map instrEssential blockInstrs)
        instrEssential = \case
          SSAReturn (Just e) -> exprUses e
          SSAReturn Nothing -> Set.empty
          SSABranch c _ _ -> exprUses c
          SSAFieldStore t _ _ v -> Set.union (exprUses t) (exprUses v)
          SSAExprStmt e -> exprUses e
          SSAAssign _ e | hasSideEffects e -> exprUses e
          _ -> Set.empty

    exprUses = \case
      SSAUse v -> Set.singleton (varKey v)
      SSAUnary _ e -> exprUses e
      SSABinary _ l r -> Set.union (exprUses l) (exprUses r)
      SSATernary c t e -> Set.unions [exprUses c, exprUses t, exprUses e]
      SSACall _ args -> Set.unions (map exprUses args)
      SSAInstanceCall t _ args -> Set.unions (exprUses t : map exprUses args)
      SSANewObject _ args -> Set.unions (map exprUses args)
      SSAFieldAccess t _ -> exprUses t
      _ -> Set.empty

    -- Use Either: Left = phi inputs, Right = expression
    buildDefMap blocks =
      let phiDefs =
            [ (varKey (phiVar phi), Left (map snd (phiArgs phi)))
            | b <- blocks
            , phi <- blockPhis b
            ]
          instrDefs =
            [ (varKey v, Right e)
            | b <- blocks
            , SSAAssign v e <- blockInstrs b
            ]
      in foldl' (\m (k, v) -> Map.insert k v m) Map.empty (phiDefs ++ instrDefs)

    propagateLive defMap initial =
      go initial (Set.toList initial)
      where
        go live [] = live
        go live (k:ks) =
          case Map.lookup k defMap of
            Nothing -> go live ks
            Just def ->
              let used = case def of
                    Right e -> exprUses e
                    Left vars -> Set.fromList (map varKey vars)
                  new = Set.difference used live
              in go (Set.union live new) (ks ++ Set.toList new)

--------------------------------------------------------------------------------
-- Copy Propagation
--------------------------------------------------------------------------------

-- | Copy propagation on SSA
ssaCopyProp :: SSAProgram -> SSAProgram
ssaCopyProp (SSAProgram classes) =
  SSAProgram [c { ssaClassMethods = map propMethod (ssaClassMethods c) } | c <- classes]
  where
    propMethod m =
      let copyPairs = findCopies (ssaMethodBlocks m)
          substMap = buildCopySubstMap copyPairs
          blocks' = map (substBlock substMap) (ssaMethodBlocks m)
      in m { ssaMethodBlocks = blocks' }

    -- Find x = y patterns, returning (dest, src) pairs
    findCopies blocks =
      [ ((ssaName v, ssaVersion v), (ssaName src, ssaVersion src))
      | b <- blocks
      , SSAAssign v (SSAUse src) <- blockInstrs b
      ]

    -- Build transitive substitution map with cycle detection
    buildCopySubstMap :: [(VarKey, VarKey)] -> Map VarKey SSAExpr
    buildCopySubstMap copies =
      let initial = Map.fromList copies
          -- Resolve chains with explicit cycle detection
          resolved = Map.mapWithKey (\k _ -> resolve Set.empty k) initial
          resolve visited key
            | Set.member key visited = key  -- Cycle detected
            | otherwise = case Map.lookup key initial of
                Nothing -> key
                Just src
                  | src == key -> key  -- Self-reference
                  | otherwise -> resolve (Set.insert key visited) src
          toExpr vk = SSAUse (SSAVar (fst vk) (snd vk) Nothing)
      in Map.map toExpr resolved

    substBlock substMap b = b
      { blockPhis = blockPhis b  -- Don't substitute phi inputs (they refer to end-of-predecessor values)
      , blockInstrs = map (substVarsInInstr substMap) (blockInstrs b)
      }

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
      case map snd (phiArgs phi) of
        -- All phi arguments are the same variable - replace with copy
        (first:rest) | all (== first) rest ->
          (phis, (phiVar phi, first) : copies)
        -- Keep the phi node
        _ -> (phi : phis, copies)

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
  SSABinary Mod _ (SSAInt 1) -> SSAInt 0  -- x % 1 = 0

  -- arithmetic with zero
  SSABinary Mul _ (SSAInt 0) -> SSAInt 0
  SSABinary Mul (SSAInt 0) _ -> SSAInt 0
  SSABinary And _ (SSAInt 0) -> SSAInt 0  -- bitwise: x & 0 = 0
  SSABinary And (SSAInt 0) _ -> SSAInt 0

  -- Self-cancellation: x - x = 0
  SSABinary Sub (SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> SSAInt 0
  -- Self-division: x / x = 1 (assuming x != 0, which semantic analysis should catch)
  SSABinary Div (SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> SSAInt 1
  -- Self-modulo: x % x = 0
  SSABinary Mod (SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> SSAInt 0

  -- Self-comparison: x == x = true, x != x = false
  SSABinary Eq (SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> SSABool True
  SSABinary Ne (SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> SSABool False
  SSABinary Lt (SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> SSABool False  -- x < x = false
  SSABinary Gt (SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> SSABool False  -- x > x = false
  SSABinary Le (SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> SSABool True   -- x <= x = true
  SSABinary Ge (SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> SSABool True   -- x >= x = true

  -- Boolean with constants
  SSABinary And e (SSABool True) -> peepholeExpr e   -- x && true = x
  SSABinary And (SSABool True) e -> peepholeExpr e
  SSABinary And _ (SSABool False) -> SSABool False   -- x && false = false
  SSABinary And (SSABool False) _ -> SSABool False
  SSABinary Or e (SSABool False) -> peepholeExpr e   -- x || false = x
  SSABinary Or (SSABool False) e -> peepholeExpr e
  SSABinary Or _ (SSABool True) -> SSABool True      -- x || true = true
  SSABinary Or (SSABool True) _ -> SSABool True

  -- Constant comparisons
  SSABinary Eq (SSAInt a) (SSAInt b) -> SSABool (a == b)
  SSABinary Ne (SSAInt a) (SSAInt b) -> SSABool (a /= b)
  SSABinary Lt (SSAInt a) (SSAInt b) -> SSABool (a < b)
  SSABinary Le (SSAInt a) (SSAInt b) -> SSABool (a <= b)
  SSABinary Gt (SSAInt a) (SSAInt b) -> SSABool (a > b)
  SSABinary Ge (SSAInt a) (SSAInt b) -> SSABool (a >= b)
  SSABinary Eq (SSABool a) (SSABool b) -> SSABool (a == b)
  SSABinary Ne (SSABool a) (SSABool b) -> SSABool (a /= b)

  -- Constant arithmetic
  SSABinary Add (SSAInt a) (SSAInt b) -> SSAInt (a + b)
  SSABinary Sub (SSAInt a) (SSAInt b) -> SSAInt (a - b)
  SSABinary Mul (SSAInt a) (SSAInt b) -> SSAInt (a * b)
  SSABinary Div (SSAInt a) (SSAInt b) | b /= 0 -> SSAInt (a `div` b)
  SSABinary Mod (SSAInt a) (SSAInt b) | b /= 0 -> SSAInt (a `mod` b)
  SSABinary And (SSABool a) (SSABool b) -> SSABool (a && b)
  SSABinary Or (SSABool a) (SSABool b) -> SSABool (a || b)

  -- Cancellation patterns: (a - b) + b = a, (a + b) - b = a
  SSABinary Add (SSABinary Sub a (SSAUse v1)) (SSAUse v2)
    | varKey v1 == varKey v2 -> peepholeExpr a
  SSABinary Sub (SSABinary Add a (SSAUse v1)) (SSAUse v2)
    | varKey v1 == varKey v2 -> peepholeExpr a

  -- Boolean absorption: a || (a && b) = a, a && (a || b) = a
  SSABinary Or a@(SSAUse v1) (SSABinary And (SSAUse v2) _)
    | varKey v1 == varKey v2 -> peepholeExpr a
  SSABinary Or a@(SSAUse v1) (SSABinary And _ (SSAUse v2))
    | varKey v1 == varKey v2 -> peepholeExpr a
  SSABinary And a@(SSAUse v1) (SSABinary Or (SSAUse v2) _)
    | varKey v1 == varKey v2 -> peepholeExpr a
  SSABinary And a@(SSAUse v1) (SSABinary Or _ (SSAUse v2))
    | varKey v1 == varKey v2 -> peepholeExpr a

  -- Boolean idempotence: a && a = a, a || a = a
  SSABinary And a@(SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> peepholeExpr a
  SSABinary Or a@(SSAUse v1) (SSAUse v2)
    | varKey v1 == varKey v2 -> peepholeExpr a

  -- Ternary with constant condition
  SSATernary (SSABool True) t _ -> peepholeExpr t
  SSATernary (SSABool False) _ e -> peepholeExpr e
  -- Ternary with same branches: cond ? x : x = x
  SSATernary _ t e | exprEqual t e -> peepholeExpr t

  -- recursively apply
  SSAUnary op e -> SSAUnary op (peepholeExpr e)
  SSABinary op l r -> SSABinary op (peepholeExpr l) (peepholeExpr r)
  SSATernary c t e -> SSATernary (peepholeExpr c) (peepholeExpr t) (peepholeExpr e)
  other -> other

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Check if two expressions are structurally equal
exprEqual :: SSAExpr -> SSAExpr -> Bool
exprEqual (SSAInt a) (SSAInt b) = a == b
exprEqual (SSABool a) (SSABool b) = a == b
exprEqual (SSAStr a) (SSAStr b) = a == b
exprEqual SSANull SSANull = True
exprEqual SSAThis SSAThis = True
exprEqual (SSAUse v1) (SSAUse v2) = varKey v1 == varKey v2
exprEqual (SSAUnary op1 e1) (SSAUnary op2 e2) = op1 == op2 && exprEqual e1 e2
exprEqual (SSABinary op1 l1 r1) (SSABinary op2 l2 r2) =
  op1 == op2 && exprEqual l1 l2 && exprEqual r1 r2
exprEqual _ _ = False
