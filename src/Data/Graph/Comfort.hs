module Data.Graph.Comfort (
   -- * types
   Graph,
   LabeledNode,
   LabeledEdge,
   Edge(from, to), defaultEdgeFoldMap,
   DirEdge(DirEdge),
   UndirEdge(UndirEdge), undirEdge,
   EitherEdge(EDirEdge,EUndirEdge),

   -- * construction
   empty, fromList, fromMap,

   -- * extract large portions of the graph
   graphMap,
   nodeLabels, nodeSet, nodes, nodeEdges,
   edgeLabels, edgeSet, edges,

   -- * queries
   isEmpty,
   lookupNode, lookupEdge,
   adjacentEdges,
   isLoop,
   pathExists,
   isConsistent,

   -- * manipulate labels
   mapNode, mapNodeWithKey,
   mapEdge, mapEdgeWithKey,
   mapNodeWithInOut, InOut,
   filterEdgeWithKey,
   traverseNode, traverseEdge, traverse,

   -- * combine graphs
   checkedZipWith,
   union,

   -- * manipulate indices
   Reverse,
   reverse,
   reverseEdge,
   mapKeys,
   mapMaybeEdgeKeys,
   mapEdgeKeys,

   -- * insertion and removal
   deleteNode, deleteNodeSet, deleteEdge,
   insertNode, insertEdge, insertEdgeSet,
   ) where

import qualified Data.Graph.Comfort.Map as MapU
import qualified Data.Graph.Comfort.TotalMap as TMap

import Control.Monad.Trans.Identity (IdentityT(IdentityT, runIdentityT))
import Data.Functor.Classes
         (Eq1(liftEq), Ord1(liftCompare), Show1(liftShowsPrec))

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Traversable as Trav
import qualified Data.Foldable as Fold
import Control.Monad (liftM2, (=<<))
import Control.Applicative (Applicative, liftA2, liftA3)
import Data.Foldable (Foldable, foldMap)
import Data.Set (Set)
import Data.Map (Map)
import Data.Monoid
         (Monoid, mempty, mappend, All(All), getAll, Endo(Endo), appEndo)
import Data.Tuple.HT (mapFst, fst3, snd3, thd3, mapFst3, mapThd3)

import qualified Test.QuickCheck as QC

import Data.Functor (Functor, fmap)
import Data.List (map, any, all, (++))
import Data.String (String)
import Data.Maybe (Maybe)
import Data.Bool (Bool(False), not, (&&), (||))
import Data.Eq (Eq, (==))
import Data.Ord (Ord, Ordering(LT,GT), (<), (>))
import Data.Tuple (uncurry)
import Data.Function (flip, (.), ($))
import Data.Int (Int)
import Text.Show
         (Show, ShowS, showParen, showString, showChar, shows, showsPrec)

import Prelude (error)


{-
For all 'Graph's the 'isConsistent' predicate must be 'True'.
-}
newtype Graph edge node edgeLabel nodeLabel =
   Graph {
      graphMapWrap ::
         Map node (InOutMap (Wrap edge) node edgeLabel nodeLabel)
   } deriving (Eq, Ord)

instance
   (Edge e, Ord n, Show1 e, Show n, Show el, Show nl) =>
      Show (Graph e n el nl) where
   showsPrec prec g =
      showParen (prec>10) $
         showString "Graph.fromList " .
         shows (Map.toList $ nodeLabels g) .
         showChar ' ' .
         shows (Map.toList $ edgeLabelsWrap g)


isConsistent :: (Ord n, Eq el) => Graph DirEdge n el nl -> Bool
isConsistent (Graph ns) =
   foldMap fst3 ns == foldMap thd3 ns
   &&
   Set.isSubsetOf
      (foldMap (foldMap (foldMap Set.singleton) . Map.keys . fst3) ns)
      (Map.keysSet ns)
   &&
   (Fold.and $ flip Map.mapWithKey ns $
      \n (ins,_nl,outs) ->
         all ((n==) . toWrap) (Map.keys ins) &&
         all ((n==) . fromWrap) (Map.keys outs))


type LabeledNode n label = (n, label)


defaultEdgeFoldMap :: (Edge edge, Monoid a) => edge a -> a
defaultEdgeFoldMap e = mappend (from e) (to e)

class (Foldable edge, Ord1 edge) => Edge edge where
   from, to :: edge node -> node

instance Edge DirEdge where
   from (DirEdge x _) = x
   to (DirEdge _ x) = x

instance Edge UndirEdge where
   from (UndirEdge x _) = x
   to (UndirEdge _ x) = x

instance Edge EitherEdge where
   from ee =
      case ee of
         EDirEdge   e -> from e
         EUndirEdge e -> from e
   to ee =
      case ee of
         EDirEdge   e -> to e
         EUndirEdge e -> to e


{-
class (Edge edge) => ConsEdge edge where
   {- |
   The construction of an edge may fail
   and it is not warranted
   that @x == from (edge x y)@ or @y == to (edge x y)@.
   -}
   edge :: Ord node => node -> node -> Maybe (edge node)

instance ConsEdge DirEdge where
   edge x y = Just $ DirEdge x y

instance ConsEdge UndirEdge where
   edge x y = Just $ undirEdge x y
-}



type LabeledEdge edge node label = (edge node, label)


data DirEdge node = DirEdge node node
   deriving (Eq, Ord, Show)

data UndirEdge node = UndirEdge node node
   deriving (Eq, Ord, Show)

undirEdge :: (Ord node) => node -> node -> UndirEdge node
undirEdge x y =
   if x<y
     then UndirEdge x y
     else UndirEdge y x

data
   EitherEdge node =
        EDirEdge (DirEdge node)
      | EUndirEdge (UndirEdge node)
   deriving (Eq, Ord, Show)


liftBin ::
   (Edge edge, Monoid a) =>
   (node0 -> node1 -> a) -> edge node0 -> edge node1 -> a
liftBin op e0 e1 = mappend (op (from e0) (from e1)) (op (to e0) (to e1))

liftEdgeEq ::
   Edge edge => (node0 -> node1 -> Bool) -> edge node0 -> edge node1 -> Bool
liftEdgeEq eq = (getAll .) . liftBin (\a b -> All $ eq a b)

liftEdgeShowsPrec ::
   (Foldable edge) =>
   String -> (Int -> node -> ShowS) -> showList -> Int -> edge node -> ShowS
liftEdgeShowsPrec name showsPrc _showsList p e =
   showParen (p>10) $
      showString name .
      appEndo (foldMap (\n -> Endo $ showChar ' ' . showsPrc 11 n) e)

instance Eq1 DirEdge where liftEq = liftEdgeEq
instance Ord1 DirEdge where liftCompare = liftBin
instance Show1 DirEdge where liftShowsPrec = liftEdgeShowsPrec "DirEdge"

instance Eq1 UndirEdge where liftEq = liftEdgeEq
instance Ord1 UndirEdge where liftCompare = liftBin
instance Show1 UndirEdge where liftShowsPrec = liftEdgeShowsPrec "UndirEdge"

instance Eq1 EitherEdge where
   liftEq eq ee0 ee1 =
      case (ee0, ee1) of
         (EDirEdge e0, EDirEdge e1) -> liftEq eq e0 e1
         (EUndirEdge e0, EUndirEdge e1) -> liftEq eq e0 e1
         _ -> False

instance Ord1 EitherEdge where
   liftCompare cmp ee0 ee1 =
      case (ee0, ee1) of
         (EDirEdge e0, EDirEdge e1) -> liftCompare cmp e0 e1
         (EUndirEdge e0, EUndirEdge e1) -> liftCompare cmp e0 e1
         (EDirEdge _, EUndirEdge _) -> LT
         (EUndirEdge _, EDirEdge _) -> GT

instance Show1 EitherEdge where
   liftShowsPrec showsPrc showsList p ee =
      case ee of
         EDirEdge e ->
            showParen (p>10) $
            showString "EDirEdge " . liftShowsPrec showsPrc showsList 11 e
         EUndirEdge e ->
            showParen (p>10) $
            showString "EUndirEdge " . liftShowsPrec showsPrc showsList 11 e


instance Functor DirEdge where
   fmap f (DirEdge x y) = DirEdge (f x) (f y)

instance Foldable DirEdge where
   foldMap f (DirEdge x y) = mappend (f x) (f y)

instance Foldable UndirEdge where
   foldMap f (UndirEdge x y) = mappend (f x) (f y)

instance Foldable EitherEdge where
   foldMap f ee =
      case ee of
         EDirEdge   e -> foldMap f e
         EUndirEdge e -> foldMap f e

instance (QC.Arbitrary n) => QC.Arbitrary (DirEdge n) where
   arbitrary = liftM2 DirEdge QC.arbitrary QC.arbitrary
   shrink (DirEdge x y) = map (uncurry DirEdge) $ QC.shrink (x,y)

instance (QC.Arbitrary n, Ord n) => QC.Arbitrary (UndirEdge n) where
   arbitrary = liftM2 undirEdge QC.arbitrary QC.arbitrary
   shrink (UndirEdge x y) =
      Set.toList $ Set.fromList $ map (uncurry undirEdge) $ QC.shrink (x,y)


graphMap ::
   Graph edge node edgeLabel nodeLabel ->
   Map node (InOutMap edge node edgeLabel nodeLabel)
graphMap = fmap unwrapInOut . graphMapWrap

nodes ::
   (Edge edge, Ord node) =>
   Graph edge node edgeLabel nodeLabel ->
   [node]
nodes = Map.keys . graphMapWrap

nodeEdges ::
   (Edge edge, Ord node) =>
   Graph edge node edgeLabel nodeLabel ->
   Map node (Set (edge node), nodeLabel, Set (edge node))
nodeEdges =
   fmap
      (\(ins,n,outs) ->
         (unwrapSet $ Map.keysSet ins, n, unwrapSet $ Map.keysSet outs)) .
   graphMapWrap


edgeLabels ::
   (Edge edge, Ord node) =>
   Graph edge node edgeLabel nodeLabel ->
   Map (edge node) edgeLabel
edgeLabels = unwrapMap . edgeLabelsWrap

edgeLabelsWrap ::
   (Edge edge, Ord node) =>
   Graph edge node edgeLabel nodeLabel ->
   Map (Wrap edge node) edgeLabel
edgeLabelsWrap = foldMap fst3 . graphMapWrap

edgeSet ::
   (Edge edge, Ord node) =>
   Graph edge node edgeLabel nodeLabel -> Set (edge node)
edgeSet = unwrapSet . foldMap (Map.keysSet . fst3) . graphMapWrap

edges ::
   (Edge edge, Ord node) =>
   Graph edge node edgeLabel nodeLabel -> [edge node]
edges = Map.keys . edgeLabels


reverse ::
   (Reverse e, Ord n) =>
   Graph e n el nl -> Graph e n el nl
reverse =
   withWrappedGraph $
   fmap
      (\(ins, nl, outs) ->
         (Map.mapKeys reverseEdgeWrap outs,
          nl,
          Map.mapKeys reverseEdgeWrap ins))

reverseEdgeWrap :: Reverse edge => Wrap edge node -> Wrap edge node
reverseEdgeWrap = wrap . reverseEdge . unwrap


class Edge edge => Reverse edge where
   reverseEdge :: edge node -> edge node

instance Reverse DirEdge where
   reverseEdge (DirEdge x y) = DirEdge y x


{- |
The index map must be an injection,
that is, nodes must not collaps.
Also the node and edge index maps must be consistent, i.e.

> from (edgeMap e) == nodeMap (from e)
> to   (edgeMap e) == nodeMap (to   e)

Strictly spoken, we would need the node map only for isolated nodes,
but we use it for all nodes for simplicity.
-}
mapKeys ::
   (Edge edge1, Ord node0, Ord node1) =>
   (node0 -> node1) ->
   (edge0 node0 -> edge1 node1) ->
   Graph edge0 node0 edgeLabel nodeLabel ->
   Graph edge1 node1 edgeLabel nodeLabel
mapKeys f g =
   withWrappedGraph $
   fmap
      (\(ins,nl,outs) ->
         (Map.mapKeys (wrap . g . unwrap) ins,
          nl,
          Map.mapKeys (wrap . g . unwrap) outs)) .
   Map.mapKeysWith (error "Graph.mapKeys: node map is not injective") f

empty :: Graph edge node edgeLabel nodeLabel
empty = Graph Map.empty

{- |
The node sets must be disjoint.
-}
union ::
   (Edge edge, Ord node) =>
   Graph edge node edgeLabel nodeLabel ->
   Graph edge node edgeLabel nodeLabel ->
   Graph edge node edgeLabel nodeLabel
union (Graph ns0) (Graph ns1) =
   Graph
      (Map.unionWith (error "Graph.union: node sets overlap") ns0 ns1)

instance
   (Edge edge, Ord node) =>
      Monoid (Graph edge node edgeLabel nodeLabel) where
   mempty = empty
   mappend = union


{- |
Node and edge sets must be equal.
-}
checkedZipWith ::
   (Edge edge, Ord node) =>
   MapU.Caller ->
   (nodeLabel0 -> nodeLabel1 -> nodeLabel2) ->
   (edgeLabel0 -> edgeLabel1 -> edgeLabel2) ->
   Graph edge node edgeLabel0 nodeLabel0 ->
   Graph edge node edgeLabel1 nodeLabel1 ->
   Graph edge node edgeLabel2 nodeLabel2
checkedZipWith caller f g (Graph ns0) (Graph ns1) =
   Graph $
   MapU.checkedZipWith (caller ++ " node")
      (\(ins0, n0, outs0) (ins1, n1, outs1) ->
         (MapU.checkedZipWith (caller ++ " ins") g ins0 ins1,
          f n0 n1,
          MapU.checkedZipWith (caller ++ " outs") g outs0 outs1))
      ns0 ns1


nodeLabels :: (Edge e, Ord n) => Graph e n el nl -> Map n nl
nodeLabels = fmap snd3 . graphMapWrap

lookupEdge :: (Edge e, Ord n) => e n -> Graph e n el nl -> Maybe el
lookupEdge e (Graph g) =
   Map.lookup (wrap e) . thd3 =<< Map.lookup (from e) g

{- |
Alternative implementation for test:
-}
_lookupEdge :: (Edge e, Ord n) => e n -> Graph e n el nl -> Maybe el
_lookupEdge e (Graph g) =
   Map.lookup (wrap e) . fst3 =<< Map.lookup (to e) g


isEmpty :: Graph e n el nl -> Bool
isEmpty = Map.null . graphMapWrap

lookupNode :: (Ord n) => n -> Graph e n el nl -> Maybe nl
lookupNode n (Graph g) = fmap snd3 $ Map.lookup n g

_pre, suc ::
   (Edge e, Ord n) =>
   Graph e n el nl -> n -> [n]
_pre g n =
   map fromWrap . Map.keys . fst3 .
   Map.findWithDefault (error "pre: unknown node") n . graphMapWrap $ g
suc g n =
   map toWrap . Map.keys . thd3 .
   Map.findWithDefault (error "suc: unknown node") n . graphMapWrap $ g

adjacentEdges ::
   (Edge e, Ord n) =>
   Graph e n el nl -> n -> Set (e n)
adjacentEdges g n =
   (\(ins,_nl,outs) ->
      unwrapSet $ Map.keysSet ins `Set.union` Map.keysSet outs) $
   Map.findWithDefault (error "adjacentEdges: unknown node") n $
   graphMapWrap g

{-
In constrast to Map.intersectWith ($), unaffected values are preserved.
-}
applyMap :: (Ord k) => Map k (a -> a) -> Map k a -> Map k a
applyMap f x =
   Map.union (Map.intersectionWith ($) f x) x

{- |
Node to be deleted must be contained in the graph.
-}
deleteNode ::
   (Edge e, Ord n) =>
   n -> Graph e n el nl -> Graph e n el nl
deleteNode n =
   withWrappedGraph $ \ns ->
   case Map.findWithDefault (error "deleteNode: unknown node") n ns of
      (ins, _nl, outs) ->
         applyMap
            (Map.mapKeys fromWrap $
             Map.mapWithKey (\e _ -> mapThd3 $ Map.delete e) ins)  $
         applyMap
            (Map.mapKeys toWrap   $
             Map.mapWithKey (\e _ -> mapFst3 $ Map.delete e) outs) $
         Map.delete n ns

{- |
Could be implemented more efficiently.
-}
deleteNodeSet ::
   (Edge e, Ord n) =>
   Set n -> Graph e n el nl -> Graph e n el nl
deleteNodeSet delNs g = Set.foldl (flip deleteNode) g delNs

deleteEdge ::
   (Edge e, Ord n) =>
   e n -> Graph e n el nl -> Graph e n el nl
deleteEdge e =
   withWrappedGraph $
      Map.adjust (mapThd3 $ Map.delete $ wrap e) (from e) .
      Map.adjust (mapFst3 $ Map.delete $ wrap e) (to e)

filterEdgeWithKey ::
   (Edge e, Ord n) =>
   (e n -> el -> Bool) ->
   Graph e n el nl -> Graph e n el nl
filterEdgeWithKey f =
   Graph .
   fmap
      (\(ins, nl, outs) ->
         (Map.filterWithKey (f . unwrap) ins, nl,
          Map.filterWithKey (f . unwrap) outs)) .
   graphMapWrap

{- |
You may only use this for filtering edges
and use more specialised types as a result.
You must not alter source and target nodes of edges.
-}
mapMaybeEdgeKeys ::
   (Edge e1, Ord n) =>
   (e0 n -> Maybe (e1 n)) ->
   Graph e0 n el nl -> Graph e1 n el nl
mapMaybeEdgeKeys f =
   withWrappedGraph $
   fmap
      (\(ins, nl, outs) ->
         (MapU.mapMaybeKeys (fmap wrap . f . unwrap) ins,
          nl,
          MapU.mapMaybeKeys (fmap wrap . f . unwrap) outs))

{- |
Same restrictions as in 'mapMaybeEdgeKeys'.
-}
mapEdgeKeys ::
   (Edge e1, Ord n) =>
   (e0 n -> e1 n) ->
   Graph e0 n el nl -> Graph e1 n el nl
mapEdgeKeys f =
   withWrappedGraph $
   fmap
      (\(ins, nl, outs) ->
         (Map.mapKeys (wrap . f . unwrap) ins,
          nl,
          Map.mapKeys (wrap . f . unwrap) outs))

{- |
In the current implementation
existing nodes are replaced with new labels
and existing edges are maintained.
However, I think we should better have an extra function for this purpose
and you should not rely on this behavior.
-}
insertNode ::
   (Ord n) => n -> nl -> Graph e n el nl -> Graph e n el nl
insertNode n nl =
   Graph .
   Map.insertWith
      (\_ (ins, _, outs) -> (ins, nl, outs))
      n (Map.empty, nl, Map.empty) .
   graphMapWrap

insertEdge ::
   (Edge e, Ord n) =>
   e n -> el -> Graph e n el nl -> Graph e n el nl
insertEdge e el = insertEdgeSet $ Map.singleton e el

{- |
In the current implementation
existing edges are replaced with new labels.
However, I think we should better have an extra function for this purpose
and you should not rely on this behavior.
It is an unchecked error if edges between non-existing nodes are inserted.
-}
insertEdgeSet ::
   (Edge e, Ord n) =>
   Map (e n) el -> Graph e n el nl -> Graph e n el nl
insertEdgeSet es =
   let ess = Map.mapWithKey Map.singleton $ wrapMap es
   in  withWrappedGraph $
       applyMap
          (fmap (\new -> mapFst3 (Map.union new)) $
           Map.mapKeysWith Map.union toWrap   ess) .
       applyMap
          (fmap (\new -> mapThd3 (Map.union new)) $
           Map.mapKeysWith Map.union fromWrap ess)

fromList ::
   (Edge e, Ord n) =>
   [LabeledNode n nl] -> [LabeledEdge e n el] -> Graph e n el nl
fromList ns es =
   fromMapWrap (Map.fromList ns) $ Map.fromList $ map (mapFst wrap) es

fromMap ::
   (Edge e, Ord n) =>
   Map n nl -> Map (e n) el -> Graph e n el nl
fromMap ns = fromMapWrap ns . wrapMap

fromMapWrap ::
   (Edge e, Ord n) =>
   Map n nl -> Map (Wrap e n) el -> Graph e n el nl
fromMapWrap ns es =
   let ess = Map.mapWithKey Map.singleton es
   in  Graph $
       TMap.intersectionPartialWith (\ins (outs, nl) -> (ins,nl,outs))
          (TMap.cons Map.empty $ Map.mapKeysWith Map.union toWrap   ess) $
       TMap.intersectionPartialWith (,)
          (TMap.cons Map.empty $ Map.mapKeysWith Map.union fromWrap ess) ns


mapNode :: (nl0 -> nl1) -> Graph e n el nl0 -> Graph e n el nl1
mapNode f =
   Graph . fmap (\(ins,n,outs) -> (ins, f n, outs)) . graphMapWrap

mapNodeWithKey :: (n -> nl0 -> nl1) -> Graph e n el nl0 -> Graph e n el nl1
mapNodeWithKey f =
   Graph .
   Map.mapWithKey (\n (ins,nl,outs) -> (ins, f n nl, outs)) .
   graphMapWrap

mapEdge :: (el0 -> el1) -> Graph e n el0 nl -> Graph e n el1 nl
mapEdge f =
   Graph . fmap (\(ins,n,outs) -> (fmap f ins, n, fmap f outs)) . graphMapWrap

mapEdgeWithKey :: (e n -> el0 -> el1) -> Graph e n el0 nl -> Graph e n el1 nl
mapEdgeWithKey f =
   Graph .
   fmap (\(ins,n,outs) -> (Map.mapWithKey (f . unwrap) ins, n, Map.mapWithKey (f . unwrap) outs)) .
   graphMapWrap

nodeSet :: Graph e n el nl -> Set n
nodeSet = Map.keysSet . graphMapWrap


type
   InOut e n el nl =
      ([LabeledEdge e n el], LabeledNode n nl, [LabeledEdge e n el])

mapNodeWithInOut ::
   (Edge e, Ord n) =>
   (InOut e n el nl0 -> nl1) -> Graph e n el nl0 -> Graph e n el nl1
mapNodeWithInOut f =
   Graph .
   Map.mapWithKey
      (\n (ins,nl,outs) ->
         (ins,
          f (Map.toList $ unwrapMap ins, (n,nl), Map.toList $ unwrapMap outs),
          outs)) .
   graphMapWrap


{- |
Same restrictions as in 'traverse'.
-}
traverseNode ::
   (Applicative f, Edge e, Ord n) =>
   (nl0 -> f nl1) -> Graph e n el nl0 -> f (Graph e n el nl1)
traverseNode f =
   fmap Graph .
   Trav.traverse (\(ins,nl0,outs) -> fmap (\nl1 -> (ins, nl1, outs)) $ f nl0) .
   graphMapWrap

{- |
Same restrictions as in 'traverse'.
-}
traverseEdge ::
   (Applicative f, Edge e, Ord n) =>
   (el0 -> f el1) -> Graph e n el0 nl -> f (Graph e n el1 nl)
traverseEdge f gr =
   fmap (fromMap (nodeLabels gr)) $ Trav.traverse f $ edgeLabels gr

{- |
Don't rely on a particular order of traversal!
-}
traverse, _traverseNaive ::
   (Applicative f, Edge e, Ord n) =>
   (nl0 -> f nl1) ->
   (el0 -> f el1) ->
   Graph e n el0 nl0 -> f (Graph e n el1 nl1)
traverse fn fe gr =
   liftA2 fromMap
      (Trav.traverse fn $ nodeLabels gr)
      (Trav.traverse fe $ edgeLabels gr)

{-
Due to the current implementation all edges are accessed twice.
That is, the actions should be commutative and non-destructive.
-}
_traverseNaive fn fe =
   fmap Graph .
   Trav.traverse
      (\(ins,n,outs) ->
         liftA3 (,,) (Trav.traverse fe ins) (fn n) (Trav.traverse fe outs)) .
   graphMapWrap


isLoop :: (Edge edge, Eq node) => edge node -> Bool
isLoop e = from e == to e

pathExists ::
   (Edge edge, Ord node) =>
   node -> node -> Graph edge node edgeLabel nodeLabel -> Bool
pathExists src dst =
   let go gr a =
          not (isEmpty gr) &&
          (a==dst || (any (go (deleteNode a gr)) $ suc gr a))
   in  flip go src


-- * Wrap utilities

type Wrap = IdentityT

wrap :: f a -> Wrap f a
wrap = IdentityT

unwrap :: Wrap f a -> f a
unwrap = runIdentityT

unwrapMap :: Map (Wrap e n) a -> Map (e n) a
unwrapMap = Map.mapKeysMonotonic unwrap

wrapMap :: Map (e n) a -> Map (Wrap e n) a
wrapMap = Map.mapKeysMonotonic wrap

unwrapSet :: Set (Wrap f a) -> Set (f a)
unwrapSet = Set.mapMonotonic unwrap


type InOutMap e n el nl = (Map (e n) el, nl, Map (e n) el)

unwrapInOut :: InOutMap (Wrap e) n el nl -> InOutMap e n el nl
unwrapInOut = mapFst3 unwrapMap . mapThd3 unwrapMap

withWrappedGraph ::
   (Map n0 (InOutMap (Wrap e0) n0 el0 nl0) ->
    Map n1 (InOutMap (Wrap e1) n1 el1 nl1)) ->
   Graph e0 n0 el0 nl0 -> Graph e1 n1 el1 nl1
withWrappedGraph f =
   Graph . f . graphMapWrap

fromWrap :: (Edge edge) => Wrap edge node -> node
fromWrap = from . unwrap

toWrap :: (Edge edge) => Wrap edge node -> node
toWrap   = to   . unwrap
