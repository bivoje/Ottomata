{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Function
import Data.List (find, groupBy, sort)
import Data.Maybe (fromJust, maybeToList)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map, (!))
import qualified Data.Map as M
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.IO as LT
import Data.GraphViz
import qualified Data.GraphViz.Printing as G
import qualified Data.GraphViz.Attributes.Complete as G
import qualified Data.GraphViz.Types.Canonical as G
import Control.Arrow


list2final :: Ord s => [s] -> s -> Bool
list2final ls s = S.member s $ S.fromList ls


-- DFA sigma initial final states alphabets
data DFA s a = DFA (s -> a -> s) s (s -> Bool) (Set s) [a]

dfa :: Ord s => (s -> a -> s) -> s -> [s] -> [s] -> [a] -> DFA s a
dfa si i fi st al = DFA si i (list2final fi) (S.fromList st) al


hop :: DFA s a -> (s -> a -> s)
hop (DFA f _ _ _ _) = f

hops :: DFA s a -> s -> [a] -> s
hops dfa = foldl $ hop dfa

isFinal :: DFA s a -> s -> Bool
isFinal (DFA _ _ final _ _) = final


class ShowAlpha a where
  showAlpha :: a -> LT.Text

instance ShowAlpha Int where
  showAlpha = LT.pack . show

instance ShowAlpha Char where
  showAlpha = LT.singleton


newtype State = Q Int deriving (Show, Read, Eq, Ord)

instance Enum State where
  toEnum = Q
  fromEnum (Q x) = x

instance PrintDot State where
  unqtDot (Q n) = unqtDot $ "q" ++ show n


dfa2dot :: (Eq s, Ord s, PrintDot s, Ord a, ShowAlpha a) => DFA s a -> LT.Text
dfa2dot dfa@(DFA _ _ _ states alphas) = G.renderDot $ toDot dotgraph
  where
    dotgraph = DotGraph False True Nothing stms
    stms = DotStmts [G.GraphAttrs [G.RankDir G.FromLeft, textLabel "DFA"]] [] nodes edges
    nodes = map (\s -> DotNode s $ nodeAttr s) $ S.toList states
    edges = map (\(f,(t,ls)) -> DotEdge f t $ showLabel ls : edgeAttr) edge_pairs
    showLabel ls = textLabel . LT.intercalate "," $ map showAlpha ls
    edge_pairs = concat [ map (s,) $ collect [ (hop dfa s a, a) | a <- alphas] | s <- S.toList states ]
    collect = map (fst . head &&& map snd) . groupBy ((==) `on` fst) . sort
    nodeAttr s = nodeShape s : [G.FontSize 8.0, G.FixedSize G.SetNodeSize, G.Width 0.3]
    nodeShape s = shape (if isFinal dfa s then DoubleCircle else Circle)
    edgeAttr = [G.FontSize 8.0, G.ArrowSize 0.3]


sample_dfa1 :: DFA State Int
sample_dfa1 = dfa sigma (Q 0) [Q 1] [Q 0 .. Q 2] [0, 1]
  where sigma (Q 0) 0 = Q 0
        sigma (Q 0) 1 = Q 1
        sigma (Q 1) 0 = Q 0
        sigma (Q 1) 1 = Q 2
        sigma (Q 2) 0 = Q 2
        sigma (Q 2) 1 = Q 1

-- prefixed with "ab"
sample_dfa2 :: DFA State Char
sample_dfa2 = dfa sigma (Q 0) [Q 2] [Q 0 .. Q 3] ['a', 'b']
  where sigma (Q 0) 'a' = Q 1
        sigma (Q 0) 'b' = Q 3
        sigma (Q 1) 'a' = Q 3
        sigma (Q 1) 'b' = Q 2
        sigma (Q 2) 'a' = Q 2
        sigma (Q 2) 'b' = Q 2
        sigma (Q 3) 'a' = Q 3
        sigma (Q 3) 'b' = Q 3

-- not containing "001"
sample_dfa3 :: DFA String Int
sample_dfa3 = dfa sigma "0" ["λ", "0", "00"] ["λ", "0", "00", "001"] [0, 1]
  where sigma "λ"   0 = "0"
        sigma "λ"   1 = "λ"
        sigma "0"   0 = "00"
        sigma "0"   1 = "λ"
        sigma "00"  0 = "00"
        sigma "00"  1 = "001"
        sigma "001" _ = "001" -- trap!

-- a[ab]*a
sample_dfa4 :: DFA State Char
sample_dfa4 = dfa sigma (Q 0) [Q 3] [Q 0 .. Q 3] ['a', 'b']
  where sigma (Q 0) 'a' = Q 2
        sigma (Q 0) 'b' = Q 1
        sigma (Q 1)  _  = Q 1 -- trap!
        sigma (Q 2) 'a' = Q 3
        sigma (Q 2) 'b' = Q 2
        sigma (Q 3) 'a' = Q 3
        sigma (Q 3) 'b' = Q 2


isRegular :: Ord s => DFA s a -> [a] -> Bool
isRegular dfa@(DFA _ initial _ _ _) = isFinal dfa . hops dfa initial


-- NFA sigma initial final states alphabets
data NFA s a = NFA (s -> Maybe a -> Set s) s (s -> Bool) (Set s) [a]

nfa :: Ord s => (s -> Maybe a -> [s]) -> s -> [s] -> [s] -> [a] -> NFA s a
nfa sigma' i final' states' al = NFA sigma i final states al
  where sigma = (S.fromList .) . sigma'
        final = list2final final'
        states = S.fromList states'


step :: NFA s a -> (s -> Maybe a -> Set s)
step (NFA f _ _ _ _) = f

atFinal :: NFA s a -> s -> Bool
atFinal (NFA _ _ final _ _) = final

valid_steps :: Ord s => NFA s a -> s -> [(s, Maybe a)] -> Bool
valid_steps nfa s ls = all id $ zipWith check (s : map fst ls) ls
  where check f (t,a) = S.member t $ step nfa f a

steps_accepted :: Ord s => NFA s a -> [(s, Maybe a)] -> Bool
steps_accepted nfa@(NFA _ initial _ _ _) steps =
  valid_steps nfa initial steps && atFinal nfa (last $ initial : map fst steps)


instance ShowAlpha a => ShowAlpha (Maybe a) where
  showAlpha Nothing = "λ"
  showAlpha (Just a) = showAlpha a


nfa2dot :: (Eq s, Ord s, PrintDot s, Ord a, ShowAlpha a) => NFA s a -> LT.Text
nfa2dot nfa@(NFA _ _ _ states alphas) = G.renderDot $ toDot dotgraph
  where
    dotgraph = DotGraph False True Nothing stms
    stms = DotStmts [G.GraphAttrs [G.RankDir G.FromLeft, textLabel "NFA"]] [] nodes edges
    nodes = map (\s -> DotNode s $ nodeAttr s) $ S.toList states
    edges = map (\(f,(t,ls)) -> DotEdge f t $ showLabel ls : edgeAttr) edge_pairs
    showLabel ls = textLabel . LT.intercalate "," $ map showAlpha ls
    edge_pairs = concat [ map (s,) $ collect [ map (,a) . S.toList $ step nfa s a | a <- Nothing : map Just alphas] | s <- S.toList states ]
    collect = map (fst . head &&& map snd) . groupBy ((==) `on` fst) . sort . concat
    nodeAttr s = nodeShape s : [G.FontSize 8.0, G.FixedSize G.SetNodeSize, G.Width 0.3]
    nodeShape s = shape (if atFinal nfa s then DoubleCircle else Circle)
    edgeAttr = [G.FontSize 8.0, G.ArrowSize 0.3]

sample_nfa1 :: NFA State Char
sample_nfa1 = nfa sigma (Q 0) [Q 3, Q 5] [Q 0 .. Q 5] ['a']
  where sigma (Q 0) (Just 'a') = [Q 1, Q 4]
        sigma (Q 1) (Just 'a') = [Q 2]
        sigma (Q 2) (Just 'a') = [Q 3]
        sigma (Q 4) (Just 'a') = [Q 5]
        sigma (Q 5) (Just 'a') = [Q 4]
        sigma _ _ = []
        -- NOTE hopping haskell optimize it & compute in compile time

sample_nfa2 :: NFA State Int
sample_nfa2 = nfa sigma (Q 0) [Q 0] [Q 0 .. Q 2] [0, 1]
  where sigma (Q 0) Nothing  = [Q 2]
        sigma (Q 0) (Just 1) = [Q 1]
        sigma (Q 1) (Just 0) = [Q 0, Q 2]
        sigma (Q 1) (Just 1) = [Q 2]
        sigma _ _ = []


dfa2nfa :: Ord s => DFA s a -> NFA s a
dfa2nfa (DFA f initial final states alphas) = NFA f' initial final states alphas
  where f' s mx = S.fromList . maybeToList $ f s <$> mx


instance PrintDot a => PrintDot (Set a) where
  unqtDot ss | S.null ss = unqtDot ("∅" :: LT.Text)
             | otherwise = G.addQuotes "'" . go $ ss
    where go = G.hcat . G.punctuate G.comma . sequenceA . map G.unqtDot . S.toAscList

bfs :: Ord s => (s -> Set s) -> s -> Set s
bfs f = bfs' f . S.singleton

bfs' :: Ord s => (s -> Set s) -> Set s -> Set s
bfs' f = bfs'' f S.empty
  where
    bfs'' f ret ss
      | S.null ss = ret
      | otherwise =
        let (s, ss') = S.deleteFindMin ss
        in if s `S.member` ret then bfs'' f ret ss' -- s already seen, ignore it
           else bfs'' f (S.insert s ret) (ss `S.union` f s)


-- it does not remove unreachable states => verbose representation.
nfa2dfa :: Ord s => NFA s a -> DFA (Set s) a
nfa2dfa (NFA f initial final states alphas) = DFA f' initial' final' states' alphas
  where f' ss a = S.unions . map (\s -> extend_lambda S.empty . f s . Just $ a) $ S.toList ss
        initial' = S.singleton initial
        final' ss = any final $ S.toList ss
        states' = S.powerSet states
          where powerset [] = [[]]
                powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs
        extend_lambda ret ss
          | S.null ss = ret
          | otherwise =
            let (s, ss') = S.deleteFindMin ss
            in if s `S.member` ret then extend_lambda ret ss'
               else extend_lambda (S.insert s ret) (ss' `S.union` f s Nothing)

sample_nfa3 :: NFA State Char
sample_nfa3 = nfa sigma (Q 0) [Q 1] [Q 0 .. Q 2] ['a', 'b']
  where sigma (Q 0) (Just 'a') = [Q 1]
        sigma (Q 1) (Just 'a') = [Q 1]
        sigma (Q 1) Nothing    = [Q 2]
        sigma (Q 2) (Just 'b') = [Q 0]
        sigma _ _ = []


sample_nfa4 :: NFA State Int
sample_nfa4 = nfa sigma (Q 0) [Q 1] [Q 0 .. Q 2] [0, 1]
  where sigma (Q 0) (Just 0) = [Q 0, Q 1]
        sigma (Q 0) (Just 1) = [Q 1]
        sigma (Q 1) (Just _) = [Q 2]
        sigma (Q 2) (Just 1) = [Q 2]
        sigma _ _ = []

removeInac :: Ord s => DFA s a -> DFA s a
removeInac (DFA si i fi _ als) = DFA si i fi accessibles als
  where accessibles = bfs (\s -> S.fromList $ map (si s) als) i

{-
digraph { # use fdp engine
    graph [rankdir=LR, label=mark];
    edge [fontsize=8, arrowsize=0.3];
    node [fontsize=8, fixedsize=true, width=0.3];

    0 [shape=circle, pos="0.0,0!"];
    1 [shape=circle, pos="1,1!"];
    2 [shape=circle, pos="1,-1!"];
    3 [shape=doublecircle, pos="2.5,1!"];
    4 [shape=doublecircle, pos="2.5,-1!"];

    0 -> 1 [label=0, color=red];
    1 -> 2 [label=0, color=red];
    2 -> 2 [label=0, color=red];
    3 -> 3 [label=0, color=red];
    4 -> 4 [label=0, color=red];

    0 -> 2 [label=1, color=blue];
    1 -> 3 [label=1, color=blue];
    2 -> 4 [label=1, color=blue];
    3 -> 3 [label=1, color=blue];
    4 -> 4 [label=1, color=blue];

    3 -> 0 [arrowhead=none, style=bold]
    3 -> 1 [arrowhead=none, style=bold]
    3 -> 2 [arrowhead=none, style=bold, color=firebrick4]

    4 -> 0 [arrowhead=none, style=bold]
    4 -> 1 [arrowhead=none, style=bold]
    4 -> 2 [arrowhead=none, style=bold, color=darkgreen]

    0 -> 1 [arrowhead=none, style=dashed, color=firebrick4]
    0 -> 2 [arrowhead=none, style=dashed, color=darkgreen]

    3 -> 4 [arrowhead=none, style=dotted]
    1 -> 2 [arrowhead=none, style=dotted]
}

the graph is redrawing of the figure 2.17 without q5 where
red and blue arrow indicates automata transition,
others indicates possible distinguishable pairs among which,
solid lines indicates pairs marked distinguishable currently, (added by step 2)
transparent lines indicates pairs WILL be marked distinguishable, (by step 3)
dotted lines indicates indistinguishable pairs that will NEVER be mared.

you can observe that we get each transparent line by pulling another solid line
(drawn in same color) along the inverse way of arrows of a color.
e.g. edge 0-2 can be get from 2-4 by pulling along blue lines, 0->2 and 2->4 in reversed way.
     edge 0-1 can be get from 2-3 by pulling along blue lines, 0->2 and 1->3 in reversed way.

it is natural inductive propagation of distinguishable property.
Inductive diff (p q : State) : Prop :=
  seed : final p ^ final q -> diff p q
  prop : exists a in alpha, diff (step p a) (step q a) -> diff p q

step 3 in `mark` procedure travels inductive propation tree in '<-' direction
which is the reason why step 3 had to repeatedly search for every cases until
no newer pairs are discovered without any clue.

however our observation is a traversal in '->' direction (of prop).
we can perform exhaustive search in same fasion as bfs (through graph of pairs),
if, we could find revese of sigma function.
-}

dfa' :: Ord a => [((Int, a), Int)] -> Int -> [Int] -> [Int] -> [a] -> DFA State a
dfa' tbl i fi st al = dfa sigma (Q i) (map Q fi) (map Q st) al
  where sigma = curry $ Q <<< (M.fromList tbl !) <<< first (\(Q n) -> n)

-- Figure 2.17
sample_dfa5 :: DFA State Int
sample_dfa5 = dfa' tbl 0 [3, 4] [0 .. 5] [0, 1]
  where tbl = [ ((0,0), 1), ((0,1), 2), ((1,0), 2), ((1,1), 3)
              , ((2,0), 2), ((2,1), 4), ((3,0), 3), ((3,1), 3)
              , ((4,0), 4), ((4,1), 4), ((5,0), 5), ((5,1), 4) ]

-- Figure 2.18
sample_dfa6 :: DFA State Int
sample_dfa6 = dfa' tbl 0 [2, 4] [0 .. 4] [0, 1]
  where tbl = [ ((0,0), 1), ((0,1), 3), ((1,0), 2), ((1,1), 4)
              , ((2,0), 1), ((2,1), 4), ((3,0), 2), ((3,1), 4)
              , ((4,0), 4), ((4,1), 4) ]

-- returns equivalence classes of indistinguishable states
indistClss :: forall s a. (Ord s, Ord a) => DFA s a -> Set (Set s)
indistClss (DFA sig _ final states alphas) = S.fromList $ map (bfs collect) sts
-- indistinguishability is equivalence relation, so that result sets are all disjoint
-- => `map (bfs collect) sts` will have (equally) duplicated sets for states that
--    are equivalent, or completely disjoint.
  where collect p = S.filter (isIndist p) states
        isIndist = curry $ not . flip S.member distinguishable
        distinguishable = bfs' propagate seeds
        propagate (p,q) = S.fromList [ (p',q') | a <- alphas, p' <- gis p a, q' <- gis q a, p' /= q']
        seeds = S.fromList [(p,q) | p <- sts, q <- sts, p /= q, final p `xor` final q]
        -- (sig :: s -> a -> s) => (gis :: s -> a -> [s]) -- inverse of sig
        gis = let maps = [((sig s a, a), [s]) | s <- sts, a <- alphas]
                  memo = foldl (flip.uncurry $ M.insertWith (++)) M.empty maps
               in curry $ flip (M.findWithDefault []) memo
        sts = S.toList states
        xor x y = not x && y || x && not y

reduce :: (Ord s, Ord a) => DFA s a -> DFA (Set s) a
reduce dfa@(DFA sig init fin _ al) = DFA sig' init' fin' states' al
  where sig' ss a = lift . (flip sig a) . sink $ ss
        init' = lift init
        fin' = fin . sink
        sink ss = S.findMin ss
        lift s  = fromJust . find (s `elem`) $ S.toList states'
        states' = indistClss dfa
