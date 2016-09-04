module Main (main) where

import qualified Data.Graph.Comfort as Graph
import Data.Graph.Comfort (Graph)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Char as Char
import Data.Bool.HT (implies)

import qualified Control.Monad.Trans.Class as MT
import qualified Control.Monad.Trans.State as MS
import Control.Applicative (liftA2, pure)
import Data.Functor.Identity (Identity(Identity), runIdentity)

import qualified Test.QuickCheck as QC



type Edge = Graph.DirEdge
type Node = Int
type EdgeLabel = Integer
type NodeLabel = Char
type MonoGraph = Graph Edge Node EdgeLabel NodeLabel

newtype TestGraph = TestGraph {getTestGraph :: MonoGraph}
   deriving (Show)

instance QC.Arbitrary TestGraph where
   shrink (TestGraph g) =
      case Graph.nodeSet g of
         ns ->
            map (TestGraph . flip Graph.deleteNodeSet g .
                 Set.difference ns . Set.fromList) $
            QC.shrink $ Set.toList ns
   arbitrary = do
      nodes <- QC.arbitrary
      fmap TestGraph $
         if null nodes
            then return Graph.empty
            else do
               let genNode = QC.elements $ map fst nodes
               fmap (Graph.fromList nodes) $ QC.listOf $
                  liftA2 (,)
                     (liftA2 Graph.DirEdge genNode genNode) QC.arbitrary


data GraphAndEdge = GraphAndEdge MonoGraph (Edge Node)
   deriving (Show)

instance QC.Arbitrary GraphAndEdge where
   shrink (GraphAndEdge gr e) =
      map (\(TestGraph g) -> GraphAndEdge g e) $ QC.shrink $ TestGraph gr
   arbitrary =
      let makeGraph p consEdge = do
            TestGraph gr <- QC.suchThat QC.arbitrary $ p . getTestGraph
            fmap (GraphAndEdge gr) $ consEdge gr
      in  QC.oneof
            [makeGraph (not . null . Graph.edges) $ QC.elements . Graph.edges,
             makeGraph (not . null . Graph.nodes) $
                \gr ->
                   let selNode = QC.elements $ Graph.nodes gr
                   in  liftA2 Graph.DirEdge selNode selNode]


test :: (QC.Testable prop) => String -> prop -> IO ()
test msg prop =
   putStr (msg ++ ": ") >> QC.quickCheck prop


emptyIsEmpty :: Bool
emptyIsEmpty =
   Graph.isEmpty (Graph.empty :: MonoGraph)

emptyIsConsistent :: Bool
emptyIsConsistent =
   Graph.isEmpty (Graph.empty :: MonoGraph)

fromMapNodeEdgeLabels :: TestGraph -> Bool
fromMapNodeEdgeLabels (TestGraph gr) =
   Graph.fromMap (Graph.nodeLabels gr) (Graph.edgeLabels gr) == gr

reverseIsConsistent :: TestGraph -> Bool
reverseIsConsistent (TestGraph gr) =
   Graph.isConsistent (Graph.reverse gr)

reverseReverse :: TestGraph -> Bool
reverseReverse (TestGraph gr) =
   Graph.reverse (Graph.reverse gr) == gr

mapNodeId :: TestGraph -> Bool
mapNodeId (TestGraph gr) =
   Graph.mapNode id gr == gr

mapEdgeId :: TestGraph -> Bool
mapEdgeId (TestGraph gr) =
   Graph.mapEdge id gr == gr

insertNodeIsConsistent :: TestGraph -> Node -> NodeLabel -> Bool
insertNodeIsConsistent (TestGraph gr) n nl =
   Graph.isConsistent $ Graph.insertNode n nl gr

insertLookupNode :: TestGraph -> Node -> NodeLabel -> Bool
insertLookupNode (TestGraph gr) n nl =
   Graph.lookupNode n (Graph.insertNode n nl gr) == Just nl

lookupNodeLabels :: TestGraph -> Node -> Bool
lookupNodeLabels (TestGraph gr) n =
   Graph.lookupNode n gr == Map.lookup n (Graph.nodeLabels gr)

deleteNodeIfExists :: Node -> MonoGraph -> MonoGraph
deleteNodeIfExists n gr =
   maybe gr (const $ Graph.deleteNode n gr) $ Graph.lookupNode n gr

deleteNodeIsConsistent :: TestGraph -> Node -> Bool
deleteNodeIsConsistent (TestGraph gr) n =
   Graph.isConsistent $ deleteNodeIfExists n gr

deleteInsertNode :: TestGraph -> Node -> NodeLabel -> Bool
deleteInsertNode (TestGraph gr) n nl =
   Graph.deleteNode n (Graph.insertNode n nl gr)
   ==
   deleteNodeIfExists n gr

insertDeleteNode :: TestGraph -> Node -> NodeLabel -> Bool
insertDeleteNode (TestGraph gr) n nl =
   let isolated =
         maybe False (const True) (Graph.lookupNode n gr)
         &&
         Set.null (Graph.adjacentEdges gr n)
   in  isolated `implies`
       Graph.insertNode n nl gr
       ==
       Graph.insertNode n nl (Graph.deleteNode n gr)


insertEdgeIsConsistent :: GraphAndEdge -> EdgeLabel -> Bool
insertEdgeIsConsistent (GraphAndEdge gr e) el =
   Graph.isConsistent $ Graph.insertEdge e el gr

insertLookupEdge :: GraphAndEdge -> EdgeLabel -> Bool
insertLookupEdge (GraphAndEdge gr e) el =
   Graph.lookupEdge e (Graph.insertEdge e el gr) == Just el

lookupEdgeLabels :: GraphAndEdge -> Bool
lookupEdgeLabels (GraphAndEdge gr e) =
   Graph.lookupEdge e gr == Map.lookup e (Graph.edgeLabels gr)

deleteEdgeIsConsistent :: GraphAndEdge -> Bool
deleteEdgeIsConsistent (GraphAndEdge gr e) =
   Graph.isConsistent $ Graph.deleteEdge e gr

deleteInsertEdge :: GraphAndEdge -> EdgeLabel -> Bool
deleteInsertEdge (GraphAndEdge gr e) el =
   Graph.deleteEdge e (Graph.insertEdge e el gr)
   ==
   Graph.deleteEdge e gr

insertDeleteEdge :: GraphAndEdge -> EdgeLabel -> Bool
insertDeleteEdge (GraphAndEdge gr e) el =
   Graph.insertEdge e el gr
   ==
   Graph.insertEdge e el (Graph.deleteEdge e gr)

filterDeleteEdge :: GraphAndEdge -> Bool
filterDeleteEdge (GraphAndEdge gr e) =
   Graph.filterEdgeWithKey (\ei _ -> e/=ei) gr == Graph.deleteEdge e gr


nodeAction :: (Monad m) => NodeLabel -> MS.StateT NodeLabel m NodeLabel
nodeAction x = do y <- MS.get; MS.put x; return y

evalTraverseNode :: NodeLabel -> MonoGraph -> MonoGraph
evalTraverseNode nl =
   flip MS.evalState nl . Graph.traverseNode nodeAction

traverseNodeIsConsistent :: TestGraph -> NodeLabel -> Bool
traverseNodeIsConsistent (TestGraph gr) nl =
   Graph.isConsistent $ evalTraverseNode nl gr


edgeAction :: (Monad m) => EdgeLabel -> MS.StateT EdgeLabel m EdgeLabel
edgeAction x = MS.modify (x+) >> MS.get

evalTraverseEdge :: EdgeLabel -> MonoGraph -> MonoGraph
evalTraverseEdge el =
   flip MS.evalState el . Graph.traverseEdge edgeAction

traverseEdgeIsConsistent :: TestGraph -> EdgeLabel -> Bool
traverseEdgeIsConsistent (TestGraph gr) el =
   Graph.isConsistent $ evalTraverseEdge el gr

evalTraverse :: NodeLabel -> EdgeLabel -> MonoGraph -> MonoGraph
evalTraverse nl el =
   flip MS.evalState el . flip MS.evalStateT nl .
   Graph.traverse nodeAction (MT.lift . edgeAction)

traverseIsConsistent :: TestGraph -> NodeLabel -> EdgeLabel -> Bool
traverseIsConsistent (TestGraph gr) nl el =
   Graph.isConsistent $ evalTraverse nl el gr


traverseNodeEdge :: TestGraph -> NodeLabel -> EdgeLabel -> Bool
traverseNodeEdge (TestGraph gr) nl el =
   evalTraverseNode nl (evalTraverseEdge el gr)
   ==
   evalTraverse nl el gr

traverseEdgeNode :: TestGraph -> NodeLabel -> EdgeLabel -> Bool
traverseEdgeNode (TestGraph gr) nl el =
   evalTraverseEdge el (evalTraverseNode nl gr)
   ==
   evalTraverse nl el gr


traverseNode :: TestGraph -> NodeLabel -> Bool
traverseNode (TestGraph gr) nl =
   flip MS.evalState nl (Graph.traverseNode nodeAction gr)
   ==
   flip MS.evalState nl (Graph.traverse nodeAction pure gr)

traverseEdge :: TestGraph -> EdgeLabel -> Bool
traverseEdge (TestGraph gr) el =
   flip MS.evalState el (Graph.traverseEdge edgeAction gr)
   ==
   flip MS.evalState el (Graph.traverse pure edgeAction gr)


traverseMapNode :: TestGraph -> Bool
traverseMapNode (TestGraph gr) =
   runIdentity (Graph.traverseNode (Identity . Char.toUpper) gr)
   ==
   Graph.mapNode Char.toUpper gr

traverseMapEdge :: TestGraph -> EdgeLabel -> Bool
traverseMapEdge (TestGraph gr) el =
   runIdentity (Graph.traverseEdge (Identity . (el+)) gr)
   ==
   Graph.mapEdge (el+) gr


main :: IO ()
main = do
   test "emptyIsEmpty" $ emptyIsEmpty
   test "emptyIsConsistent" $ emptyIsConsistent
   test "fromMapNodeEdgeLabels" $ fromMapNodeEdgeLabels
   test "reverseIsConsistent" $ reverseIsConsistent
   test "reverseReverse" $ reverseReverse
   test "mapNodeId" $ mapNodeId
   test "mapEdgeId" $ mapEdgeId

   test "insertNodeIsConsistent" $ insertNodeIsConsistent
   test "insertLookupNode" $ insertLookupNode
   test "lookupNodeLabels" $ lookupNodeLabels
   test "deleteNodeIsConsistent" $ deleteNodeIsConsistent
   test "deleteInsertNode" $ deleteInsertNode
   test "insertDeleteNode" $ insertDeleteNode

   test "insertEdgeIsConsistent" $ insertEdgeIsConsistent
   test "insertLookupEdge" $ insertLookupEdge
   test "lookupEdgeLabels" $ lookupEdgeLabels
   test "deleteEdgeIsConsistent" $ deleteEdgeIsConsistent
   test "deleteInsertEdge" $ deleteInsertEdge
   test "insertDeleteEdge" $ insertDeleteEdge
   test "filterDeleteEdge" $ filterDeleteEdge

   test "traverseNodeIsConsistent" $ traverseNodeIsConsistent
   test "traverseEdgeIsConsistent" $ traverseEdgeIsConsistent
   test "traverseIsConsistent" $ traverseIsConsistent
   test "traverseNodeEdge" $ traverseNodeEdge
   test "traverseEdgeNode" $ traverseEdgeNode
   test "traverseNode" $ traverseNode
   test "traverseEdge" $ traverseEdge
   test "traverseMapNode" $ traverseMapNode
   test "traverseMapEdge" $ traverseMapEdge
