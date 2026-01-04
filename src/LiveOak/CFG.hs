{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

-- | Control Flow Graph (CFG) representation for LiveOak SSA.
-- Provides proper predecessor/successor relationships and graph traversals
-- needed for dominance analysis and phi node placement.
module LiveOak.CFG
  ( -- * Types
    CFG(..)
  , CFGBlock(..)
  , Terminator(..)
  , BlockId

    -- * Construction
  , buildCFG
  , cfgFromBlocks

    -- * Graph Queries
  , predecessors
  , successors
  , allBlockIds
  , getBlock
  , entryBlock
  , exitBlocks

    -- * Traversals
  , reversePostorder
  , postorder
  , dfs

    -- * Utilities
  , validateCFG

    -- * Critical Edge Splitting
  , isCriticalEdge
  , findCriticalEdges
  , splitCriticalEdges
  , splitEdge
  ) where

import LiveOak.SSATypes (SSABlock(..), SSAInstr(..), SSAMethod(..), PhiNode(..), SSAExpr)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (foldl')

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Block identifier (label)
type BlockId = String

-- | Block terminator - determines control flow to successors
data Terminator
  = TermJump !BlockId                      -- ^ Unconditional jump
  | TermBranch !SSAExpr !BlockId !BlockId  -- ^ Conditional branch (cond, true, false)
  | TermReturn !(Maybe SSAExpr)            -- ^ Return from method
  deriving (Eq, Show)

-- | CFG block with explicit terminator
data CFGBlock = CFGBlock
  { cfgBlockId :: !BlockId
  , cfgPhis :: ![PhiNode]         -- ^ Phi functions at block start
  , cfgInstrs :: ![SSAInstr]      -- ^ Instructions (excluding terminators)
  , cfgTerm :: !Terminator        -- ^ Block terminator
  } deriving (Eq, Show)

-- | Control Flow Graph
data CFG = CFG
  { cfgBlocks :: !(Map BlockId CFGBlock)  -- ^ All blocks
  , cfgEntry :: !BlockId                   -- ^ Entry block
  , cfgPreds :: !(Map BlockId [BlockId])   -- ^ Predecessor map (precomputed)
  , cfgSuccs :: !(Map BlockId [BlockId])   -- ^ Successor map (precomputed)
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

-- | Build a CFG from an SSA method
buildCFG :: SSAMethod -> CFG
buildCFG SSAMethod{..} = cfgFromBlocks ssaEntryBlock ssaMethodBlocks

-- | Build a CFG from a list of SSA blocks
cfgFromBlocks :: BlockId -> [SSABlock] -> CFG
cfgFromBlocks entry blocks =
  let cfgBlockList = map convertBlock blocks
      blockMap = Map.fromList [(cfgBlockId b, b) | b <- cfgBlockList]
      -- Compute successors from terminators
      succMap = Map.fromList [(cfgBlockId b, termSuccessors (cfgTerm b)) | b <- cfgBlockList]
      -- Compute predecessors by inverting successors
      predMap = computePredecessors succMap
  in CFG
    { cfgBlocks = blockMap
    , cfgEntry = entry
    , cfgPreds = predMap
    , cfgSuccs = succMap
    }

-- | Convert an SSA block to a CFG block
convertBlock :: SSABlock -> CFGBlock
convertBlock SSABlock{..} =
  let (instrs, term) = splitTerminator blockLabel blockInstrs
  in CFGBlock
    { cfgBlockId = blockLabel
    , cfgPhis = blockPhis
    , cfgInstrs = instrs
    , cfgTerm = term
    }

-- | Split instructions into non-terminators and terminator
-- Empty blocks (like join blocks) get a void return terminator
splitTerminator :: String -> [SSAInstr] -> ([SSAInstr], Terminator)
splitTerminator _blockId instrs =
  case reverse instrs of
    [] -> ([], TermReturn Nothing)  -- Empty block gets void return (can be optimized away later)
    (last':rest) ->
      case instrToTerm last' of
        Just term -> (reverse rest, term)
        Nothing -> (instrs, TermReturn Nothing)  -- No explicit terminator, add implicit return

-- | Try to convert an instruction to a terminator
instrToTerm :: SSAInstr -> Maybe Terminator
instrToTerm = \case
  SSAJump target -> Just $ TermJump target
  SSABranch cond thenB elseB -> Just $ TermBranch cond thenB elseB
  SSAReturn expr -> Just $ TermReturn expr
  _ -> Nothing

-- | Get successors from a terminator
termSuccessors :: Terminator -> [BlockId]
termSuccessors = \case
  TermJump target -> [target]
  TermBranch _ thenB elseB -> [thenB, elseB]
  TermReturn _ -> []

-- | Compute predecessors by inverting successor map
computePredecessors :: Map BlockId [BlockId] -> Map BlockId [BlockId]
computePredecessors succMap =
  let -- Start with empty predecessor lists for all blocks
      allBlocks = Map.keysSet succMap `Set.union`
                  Set.fromList (concat $ Map.elems succMap)
      emptyPreds = Map.fromSet (const []) allBlocks
      -- Add predecessor edges
      addEdge preds (from, to) =
        Map.insertWith (++) to [from] preds
      edges = [(from, to) | (from, tos) <- Map.toList succMap, to <- tos]
  in foldl' addEdge emptyPreds edges

--------------------------------------------------------------------------------
-- Graph Queries
--------------------------------------------------------------------------------

-- | Get predecessors of a block
predecessors :: CFG -> BlockId -> [BlockId]
predecessors cfg bid = Map.findWithDefault [] bid (cfgPreds cfg)

-- | Get successors of a block
successors :: CFG -> BlockId -> [BlockId]
successors cfg bid = Map.findWithDefault [] bid (cfgSuccs cfg)

-- | Get all block IDs
allBlockIds :: CFG -> [BlockId]
allBlockIds = Map.keys . cfgBlocks

-- | Get a block by ID
getBlock :: CFG -> BlockId -> Maybe CFGBlock
getBlock cfg bid = Map.lookup bid (cfgBlocks cfg)

-- | Get the entry block
entryBlock :: CFG -> Maybe CFGBlock
entryBlock cfg = getBlock cfg (cfgEntry cfg)

-- | Get all exit blocks (blocks with TermReturn)
exitBlocks :: CFG -> [BlockId]
exitBlocks cfg =
  [ cfgBlockId b
  | b <- Map.elems (cfgBlocks cfg)
  , isExit (cfgTerm b)
  ]
  where
    isExit (TermReturn _) = True
    isExit _ = False

--------------------------------------------------------------------------------
-- Traversals
--------------------------------------------------------------------------------

-- | Depth-first search from entry, returning blocks in visit order
dfs :: CFG -> [BlockId]
dfs cfg = go Set.empty [cfgEntry cfg]
  where
    go _ [] = []
    go visited (b:bs)
      | Set.member b visited = go visited bs
      | otherwise =
          b : go (Set.insert b visited) (successors cfg b ++ bs)

-- | Postorder traversal (children before parent)
postorder :: CFG -> [BlockId]
postorder cfg = snd $ go Set.empty [] (cfgEntry cfg)
  where
    go visited acc bid
      | Set.member bid visited = (visited, acc)
      | otherwise =
          let visited' = Set.insert bid visited
              (visited'', acc') = foldl (\(v, a) s -> go v a s)
                                        (visited', acc)
                                        (successors cfg bid)
          in (visited'', acc' ++ [bid])  -- Append bid after visiting children

-- | Reverse postorder traversal (parent before children)
-- This is the order needed for forward dataflow analysis
reversePostorder :: CFG -> [BlockId]
reversePostorder = reverse . postorder

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate CFG structure
validateCFG :: CFG -> [String]
validateCFG cfg = concat
  [ validateEntry
  , validateBlocks
  , validateEdges
  ]
  where
    validateEntry
      | Map.member (cfgEntry cfg) (cfgBlocks cfg) = []
      | otherwise = ["Entry block '" ++ cfgEntry cfg ++ "' not found"]

    validateBlocks =
      [ "Block '" ++ bid ++ "' referenced but not defined"
      | bid <- referencedBlocks
      , not $ Map.member bid (cfgBlocks cfg)
      ]

    referencedBlocks =
      Set.toList $ Set.fromList $ concat
        [ termSuccessors (cfgTerm b)
        | b <- Map.elems (cfgBlocks cfg)
        ]

    validateEdges =
      -- Check that successor/predecessor maps are consistent
      [ "Inconsistent edge: " ++ from ++ " -> " ++ to
      | (from, tos) <- Map.toList (cfgSuccs cfg)
      , to <- tos
      , from `notElem` predecessors cfg to
      ]

--------------------------------------------------------------------------------
-- Critical Edge Splitting
--------------------------------------------------------------------------------

-- | Check if an edge is critical
-- A critical edge goes from a block with multiple successors
-- to a block with multiple predecessors
isCriticalEdge :: CFG -> BlockId -> BlockId -> Bool
isCriticalEdge cfg from to =
  hasMultiple (successors cfg from) && hasMultiple (predecessors cfg to)
  where
    hasMultiple (_:_:_) = True  -- At least 2 elements
    hasMultiple _ = False

-- | Find all critical edges in the CFG
findCriticalEdges :: CFG -> [(BlockId, BlockId)]
findCriticalEdges cfg =
  [ (from, to)
  | from <- allBlockIds cfg
  , to <- successors cfg from
  , isCriticalEdge cfg from to
  ]

-- | Split all critical edges in the CFG
-- Returns the new CFG and a list of created blocks
splitCriticalEdges :: CFG -> (CFG, [(BlockId, BlockId, BlockId)])
splitCriticalEdges cfg =
  let criticals = findCriticalEdges cfg
  in foldl' splitOne (cfg, []) (zip [0..] criticals)
  where
    splitOne (c, created) (n, (from, to)) =
      let newBlockId = "__split_" ++ show n ++ "__"
          (c', _) = splitEdge c from to newBlockId
      in (c', (from, to, newBlockId) : created)

-- | Split a single edge by inserting a new block
-- Returns the modified CFG and the new block
splitEdge :: CFG -> BlockId -> BlockId -> BlockId -> (CFG, CFGBlock)
splitEdge cfg from to newBlockId =
  let -- Create the new block (just jumps to the target)
      newBlock = CFGBlock
        { cfgBlockId = newBlockId
        , cfgPhis = []
        , cfgInstrs = []
        , cfgTerm = TermJump to
        }

      -- Update the source block's terminator to point to new block
      updateTerm = \case
        TermJump t | t == to -> TermJump newBlockId
        TermBranch cond thenB elseB ->
          TermBranch cond
            (if thenB == to then newBlockId else thenB)
            (if elseB == to then newBlockId else elseB)
        other -> other

      -- Update source block
      blocks' = case Map.lookup from (cfgBlocks cfg) of
        Just b -> Map.insert from (b { cfgTerm = updateTerm (cfgTerm b) }) (cfgBlocks cfg)
        Nothing -> cfgBlocks cfg

      -- Add new block
      blocks'' = Map.insert newBlockId newBlock blocks'

      -- Update phi nodes in target block to reference new block
      blocks''' = case Map.lookup to blocks'' of
        Just targetBlock ->
          let phis' = map (updatePhiPred from newBlockId) (cfgPhis targetBlock)
          in Map.insert to (targetBlock { cfgPhis = phis' }) blocks''
        Nothing -> blocks''

      -- Rebuild successor/predecessor maps
      succMap = Map.fromList [(cfgBlockId b, termSuccessors (cfgTerm b)) | b <- Map.elems blocks''']
      predMap = computePredecessors succMap

  in ( cfg { cfgBlocks = blocks''', cfgSuccs = succMap, cfgPreds = predMap }
     , newBlock
     )

-- | Update a phi node to replace one predecessor with another
updatePhiPred :: BlockId -> BlockId -> PhiNode -> PhiNode
updatePhiPred oldPred newPred phi@PhiNode{..} =
  phi { phiArgs = map updateArg phiArgs }
  where
    updateArg (predBlock, var)
      | predBlock == oldPred = (newPred, var)
      | otherwise = (predBlock, var)
