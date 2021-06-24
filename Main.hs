{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Function
import Data.List (groupBy, sort, find)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as N
import Data.Maybe (fromJust, maybeToList)
import Data.Monoid (Endo (..))
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
import Control.Monad
import qualified Control.Monad.State as ST


infixr 8 .+
(.+) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.+) g f a b = g $ f a b

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

collectEdges :: (Ord s, Ord a) => (s -> a -> [s]) -> Set s -> [a] -> [(s,s, NonEmpty a)]
collectEdges sig sts al = [ (f,t,ls) | f <- S.toList sts, (ls,t) <- deref (sprouts f) ]
  where --sprouts :: s -> [(a, [s])] -- collection of (dests, transition) from a state
        sprouts s = [ (a, sig s a) | a <- al]
        --deref :: [(a, [s])] -> [([a], s)] -- both deeply sorted
        deref = map (N.fromList . map fst &&& snd . head) . groupBy ((==) `on` snd) . sort . flatr
          -- FIXME optimize sorting
          where flatr = (uncurry (map . (,)) =<<) :: [(a,[s])] -> [(a, s)]

dfa2dot :: (Eq s, Ord s, PrintDot s, Ord a, ShowAlpha a) => DFA s a -> LT.Text
dfa2dot dfa@(DFA sig _ _ states alphas) = G.renderDot $ toDot dotgraph
  where
    dotgraph = DotGraph False True Nothing stms
    stms = DotStmts [graphAttr, nodeAttr, edgeAttr] [] nodes edges
    nodes = map (\s -> DotNode s [nodeShape s]) $ S.toList states
    edges = map (\(f,t,ls) -> DotEdge f t [showLabel ls]) edge_pairs
    showLabel ls = textLabel . LT.intercalate "," . map showAlpha $ N.toList ls
    edge_pairs = collectEdges ((:[]) .+ sig) states alphas
    nodeShape s = shape (if isFinal dfa s then DoubleCircle else Circle)
    graphAttr = G.GraphAttrs [G.RankDir G.FromLeft, textLabel "DFA"]
    nodeAttr  = G.NodeAttrs  [G.FontSize 8.0, G.FixedSize G.SetNodeSize, G.Width 0.3]
    edgeAttr  = G.EdgeAttrs  [G.FontSize 8.0, G.ArrowSize 0.3]


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

-- almost equal to dfa2dot...
nfa2dot :: (Eq s, Ord s, PrintDot s, Ord a, ShowAlpha a) => NFA s a -> LT.Text
nfa2dot nfa@(NFA sig _ _ states alphas) = G.renderDot $ toDot dotgraph
  where
    dotgraph = DotGraph False True Nothing stms
    stms = DotStmts [graphAttr, nodeAttr, edgeAttr] [] nodes edges
    nodes = map (\s -> DotNode s [nodeShape s]) $ S.toList states
    edges = map (\(f,t,ls) -> DotEdge f t [showLabel ls]) edge_pairs
    showLabel ls = textLabel . LT.intercalate "," . map showAlpha $ N.toList ls
    edge_pairs = collectEdges (S.toList .+ sig) states (Nothing : map Just alphas)
    nodeShape s = shape (if atFinal nfa s then DoubleCircle else Circle)
    graphAttr = G.GraphAttrs [G.RankDir G.FromLeft, textLabel "DFA"]
    nodeAttr  = G.NodeAttrs  [G.FontSize 8.0, G.FixedSize G.SetNodeSize, G.Width 0.3]
    edgeAttr  = G.EdgeAttrs  [G.FontSize 8.0, G.ArrowSize 0.3]


-- Figure 2.8
sample_nfa1 :: NFA State Char
sample_nfa1 = nfa sigma (Q 0) [Q 3, Q 5] [Q 0 .. Q 5] ['a']
  where sigma (Q 0) (Just 'a') = [Q 1, Q 4]
        sigma (Q 1) (Just 'a') = [Q 2]
        sigma (Q 2) (Just 'a') = [Q 3]
        sigma (Q 4) (Just 'a') = [Q 5]
        sigma (Q 5) (Just 'a') = [Q 4]
        sigma _ _ = []
        -- NOTE hopping haskell optimize it & compute in compile time

-- Figure 2.9
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
nfa2dfa :: (Ord s, Ord a) => NFA s a -> DFA (Set s) a
nfa2dfa (NFA f initial final states alphas) = DFA f' initial' final' states' alphas
  where f' ss a = S.unions . map (\s -> extend_lambda . f s . Just $ a) $ S.toList ss
          where extend_lambda = bfs' (\s -> f s Nothing)
        initial' = S.singleton initial
        final' ss = any final $ S.toList ss
        -- NOTE S.toList works as iterator for a set (due to lazyness)
        states' = S.powerSet states

-- Figure 2.12
sample_nfa3 :: NFA State Char
sample_nfa3 = nfa sigma (Q 0) [Q 1] [Q 0 .. Q 2] ['a', 'b']
  where sigma (Q 0) (Just 'a') = [Q 1]
        sigma (Q 1) (Just 'a') = [Q 1]
        sigma (Q 1) Nothing    = [Q 2]
        sigma (Q 2) (Just 'b') = [Q 0]
        sigma _ _ = []

-- Figure 2.14
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

-- procedure of `mark`
mark :: (Ord s, Ord a) => DFA s a -> s -> s -> Bool
mark (DFA sig _ final states alphas) p q =
  let distinguishables = bfs' propagate seeds
   in flip S.member distinguishables $ up p q
  where -- propagates to next distinguishable pairs
        propagate (p,q) = S.fromList [ up p' q' | a <- alphas, p' <- gis p a, q' <- gis q a, p' /= q']
        -- strict UR half of sorted sts * sorted sts, filterd by xor-final
        seeds = S.fromList [up p q | p <- sts, q <- sts, p /= q, final p `xor` final q]
        -- (sig :: s -> a -> s) => (gis :: s -> a -> [s]) -- inverse of sig
        gis = let maps = [((sig s a, a), [s]) | s <- sts, a <- alphas]
                  memo = foldl (flip.uncurry $ M.insertWith (++)) M.empty maps
               in curry $ flip (M.findWithDefault []) memo
        sts = S.toList states
        xor x y = not x && y || x && not y
        up :: Ord s => s -> s -> (s,s) -- creates unordered pair
        up x y = if compare x y == LT then (x,y) else (y,x)

reduceIndist :: forall s a. (Ord s, Ord a) => DFA s a -> DFA (Set s) a
reduceIndist dfa@(DFA sig init fin states al) =
  let sig' ss a = lift . (flip sig a) . sink $ ss
      (init', fin') = (lift init, fin . sink)
      states' = S.fromList $ map (bfs lift) $ S.toList states
   in DFA sig' init' fin' states' al
  where sink ss = S.findMin ss
        lift p = S.filter (isIndist p) states
        isIndist p q = not $ marked p q
        marked = mark dfa


sample_dfa7 :: DFA State Int
sample_dfa7 = dfa sigma (Q 0) [Q 1] [Q 0 .. Q 25] [0, 1, 2]
  where sigma (Q n) a = Q . (`mod` 26) . fibo . (+ a) $ n
        fibo 0 = 1
        fibo 1 = 1
        fibo n = fibo (n-1) + fibo (n-2)

-- makes sigma produce fater using memoization
quicker :: (Ord s, Ord a) => DFA s a -> DFA s a
quicker (DFA sigma i final states alphas) = DFA sigma' i final' states alphas
  where sigma' = curry (M.fromSet (uncurry sigma) inputs !)
        inputs = S.fromList [(s,a) | a <- alphas, s <- S.toList states]
        final' = (M.fromSet final states !)

rename :: forall t s a. (Ord t, Ord s) => Set t -> DFA s a -> DFA t a
rename states' (DFA sigma init fin states al) = DFA sigma' init' fin' states' al
  where conv = flip S.elemAt states' . flip S.findIndex states :: s -> t
        conv' = flip S.elemAt states . flip S.findIndex states' :: t -> s
        sigma' = flip (\a -> conv . flip sigma a . conv')
        init' = conv init
        fin' = fin . conv'


type Inc n = ST.State n

next :: Enum n => Inc n n
next = ST.get >>= \n -> ST.modify succ >> return n

runInc :: Inc n a -> n -> (a, n)
runInc = ST.runState


newtype SigBuilder s a = SigBuilder { build :: s -> Maybe a -> Set s }

wire :: (Ord s, Eq a) => s -> Maybe a -> s -> SigBuilder s a -> SigBuilder s a
wire init malpha fin sb = SigBuilder $ \s ma ->
  if s == init && ma == malpha then fin `S.insert` build sb s ma
  else build sb s ma

instance Ord s => Semigroup (SigBuilder s a) where
  sb1 <> sb2 = SigBuilder $ \s ma ->
    build sb1 s ma `S.union` build sb2 s ma

instance Ord s => Monoid (SigBuilder s a) where
  mempty = SigBuilder $ const (const S.empty)


data NFA' s a = NFA' (SigBuilder s a) s s


-- Rex is strict to force finite structure
data Rex a
  = Nill
  | Prim !(Maybe a)
  | Alt !(Rex a) !(Rex a)
  | Cat !(Rex a) !(Rex a)
  | Clos !(Rex a)
  deriving (Show, Read, Eq)

-- implemented Num only to utilize operators.
-- as in http://hackage.haskell.org/package/algebraic-graphs-0.4/docs/Algebra-Graph.html#t:Graph
instance Num (Rex a) where
  (+) = Alt
  (*) = Cat
  abs = undefined
  signum = undefined
  fromInteger 0 = Nill
  fromInteger _ = undefined
  negate = undefined

λ :: Rex a
λ = Prim Nothing

ε :: a -> Rex a
ε = Prim . Just

-- Figure 3.6 (0+11)*(10*+2)
sample_rex1 :: Rex Int
sample_rex1 = (Clos $ ε 0 + ε 1 * ε 1) * (ε 1 * Clos (ε 0) + ε 2)


instance ShowAlpha a => ShowAlpha (Rex a) where
  showAlpha rex = go rex where
    go (Nill)         = "∅"
    go (Prim Nothing) = "λ"
    go (Prim (Just a)) = showAlpha a
    go (Alt r1 r2) = wrap 0 r1 +++ "+" +++ wrap 0 r2
    go (Cat r1 r2) = wrap 1 r1 +++         wrap 1 r2
    go (Clos r) = wrap 2 r +++ "*"
    wrap :: Int -> Rex a -> LT.Text
    wrap n r = if rexPrec r >= n then go r
               else "(" +++ go r +++ ")"
    rexPrec (Alt _ _) = 0
    rexPrec (Cat _ _) = 1
    rexPrec (Clos _)  = 2
    rexPrec _ = 3
    (+++) = LT.append

rex2nfa :: Ord a => Rex a -> NFA State a
rex2nfa rex =
  let (NFA' sig init fin, q) = runInc (rex2nfa' rex) (Q 0)
      states = S.fromList [Q 0 .. pred q]
      alphabets = S.toList $ rex2alphas rex
   in NFA (build sig) init (==fin) states alphabets

rex2alphas :: Ord a => Rex a -> Set a
rex2alphas (Prim (Just a)) = S.singleton a
rex2alphas (Alt nl nr) = (S.union `on` rex2alphas) nl nr
rex2alphas (Cat nl nr) = (S.union `on` rex2alphas) nl nr
rex2alphas (Clos na) = rex2alphas na
rex2alphas _ = S.empty

-- generates nfa that follows conversion rules strictly
rex2nfa' :: (Enum s, Ord s, Ord a) => Rex a -> Inc s (NFA' s a)
rex2nfa' Nill = NFA' mempty <$> next <*> next
rex2nfa' (Prim ma) = do
  (init, fin) <- (,) <$> next <*> next
  return $ NFA' (mempty & wire init ma fin) init fin
rex2nfa' (Alt nl nr) = do
  init <- next
  NFA' sigl initl finl <- rex2nfa' nl
  NFA' sigr initr finr <- rex2nfa' nr
  fin <- next
  let sig = sigl <> sigr
            & wire init Nothing initl
            & wire init Nothing initr
            & wire finl Nothing fin
            & wire finr Nothing fin
  return $ NFA' sig init fin
rex2nfa' (Cat nl nr) = do
  NFA' sigl initl finl <- rex2nfa' nl
  NFA' sigr initr finr <- rex2nfa' nr
  let sig = sigl <> sigr & wire finl Nothing initr
  return $ NFA' sig initl finr
rex2nfa' (Clos na) = do
  NFA' sig' init fin <- rex2nfa' na
  let sig = sig'
            & wire init Nothing fin
            & wire fin Nothing init
  return $ NFA' sig init fin


rex2nfa_simpler :: Ord a => Rex a -> NFA State a
rex2nfa_simpler rex =
  let (sig, q) = runInc (rex2nfa'' rex (Q 0) (Q 1)) (Q 2)
      states = S.fromList [Q 0 .. pred q]
      alphabets = S.toList $ rex2alphas rex
   in NFA (build sig) (Q 0) (== Q 1) states alphabets

-- gnerates more simpler nfa (omitting redundant lambda transitions..)
-- validity is not guaranteed
rex2nfa'' :: (Enum s, Ord s, Eq a) => Rex a -> s -> s -> Inc s (SigBuilder s a)
rex2nfa'' Nill _ _ = return mempty
rex2nfa'' (Prim ma) i f = return $ mempty & wire i ma f
rex2nfa'' (Alt nl nr) i f = do
  sigl <- rex2nfa'' nl i f
  sigr <- rex2nfa'' nr i f
  return $ sigl <> sigr
rex2nfa'' (Cat nl nr) i f = do
  mid <- next
  sigl <- rex2nfa'' nl i mid
  sigr <- rex2nfa'' nr mid f
  return $  sigl <> sigr
rex2nfa'' (Clos na) i f = do
  (init, fin) <- (,) <$> next <*> next
  sig <- rex2nfa'' na init fin
  return $ sig
           & wire init Nothing fin
           & wire fin Nothing init
           & wire i Nothing init
           & wire fin Nothing f
{- FIXME it does not generate neither smallest nor correct for sample_rex1
  rex2nfa'' (Clos na) i f = do
  sig <- rex2nfa'' na i f
  return $ sig
           & wire i Nothing f
           & wire f Nothing i-}

-- Example 3.8 a*+a*(a+b)c*
sample_rex2 :: Rex Char
sample_rex2 = (Clos $ ε 'a') + (Clos $ ε 'a') * (ε 'a' + ε 'b') * (Clos $ ε 'c')


-- (complete) Generalized Transfer Graph
-- keeps list of nodes (staets) in the graph
-- where [fin, init] is the last elem
data GTG s a = GTG
  { getRexMap :: Map (s,s) (Rex a)
  , getStates :: [s]
  } deriving (Show, Read, Eq)

splitLast2 :: [a] -> ([a], [a])
splitLast2 [] = ([],[])
splitLast2 [a] = ([],[a])
splitLast2 [a,b] = ([],[a,b])
splitLast2 (c:ab) = first (c:) $ splitLast2 ab


monofinNFA :: (Ord s, Eq a) => s -> NFA s a -> (NFA s a, s)
monofinNFA fin' nfa@(NFA sig ini final states al) =
  let fins = filter final $ S.toList states
      wires = map (\f -> Endo $ wire f Nothing fin') fins -- isn't it sub-optimal? `if s `elem` fins -> fin' ???
      sig' = build . appEndo (mconcat wires) $ SigBuilder sig
      states' = fin' `S.insert` states
      nfa' = NFA sig' ini (==fin') states' al
   in case fins of
        [f] | f /= ini -> (nfa, f)
        _ -> (nfa', fin')

nfa2gtg :: (Ord s, Ord a) => s -> NFA s a -> GTG s a
nfa2gtg fin' nfa =
  let (NFA sig ini _ states alphas, fin) = monofinNFA fin' nfa
      edge_pairs = collectEdges (S.toList .+ sig) states (Nothing : map Just alphas)
      partial = foldl (\m (f,t,ls) -> M.insert (f,t) (as2r ls) m) M.empty edge_pairs
      full = foldl insertDummy partial [(p,q) | p <- S.toList states, q <- S.toList states ]
      states' = S.toList . S.delete fin . S.delete ini $ states
   in GTG full $ states' ++ [ini, fin]
  where as2r (a:|[]) = Prim a
        as2r as = let (ls, rs) = halve as in (Alt `on` as2r) ls rs
        halve xs = -- halve assumes `length xs >= 2`
          let n = (length xs) `div` 2
           in (N.fromList $ N.take n xs, N.fromList $ N.drop n xs)
        insertDummy m pq = M.insertWith (flip const) pq Nill m


gtg2dot :: (PrintDot s, ShowAlpha a) => GTG s a -> LT.Text
gtg2dot (GTG m ss) = G.renderDot $ toDot dotgraph
  where
    dotgraph = DotGraph False True Nothing stms
    stms = DotStmts [graphAttr, nodeAttr, edgeAttr] [] nodes edges
    nodes = uncurry (++) <<< circle *** dcircle <<< init &&& (:[]) . last $ ss
      where circle  = map $ flip DotNode [shape Circle]
            dcircle = map $ flip DotNode [shape DoubleCircle]
    edges = map (\((f,t),r) -> DotEdge f t [textLabel $ showAlpha r]) $ M.toList m
    graphAttr = G.GraphAttrs [G.RankDir G.FromLeft, textLabel "GTG"]
    nodeAttr  = G.NodeAttrs  [G.FontSize 8.0, G.FixedSize G.SetNodeSize, G.Width 0.3]
    edgeAttr  = G.EdgeAttrs  [G.FontSize 8.0, G.ArrowSize 0.3]


gtg2rex' :: Ord s => GTG s a -> Rex a
gtg2rex' gtg@(GTG m states) = case states of
  -- DFA/NFA has at least 1 state (initial)
  -- GTG has at least 2 states (initial, monofin)
  [ini, fin] ->
    let r1 = m ! (ini, ini)
        r2 = m ! (ini, fin)
        r3 = m ! (fin, ini)
        r4 = m ! (fin, fin)
        r1' = Clos r1
     in r1' * r2 * Clos (r4 + r3 * r1' * r2)
  _ -> gtg2rex' . reduceGTG $ gtg

reduceGTG :: forall s a. Ord s => GTG s a -> GTG s a
reduceGTG (GTG m (s:ss)) =
  let withS (p,q) = p == s || q == s
      updates = [alienate p s q | p <- ss, q <- ss, p /= q]
      removal = Endo $ M.filterWithKey (const . not . withS)
      m' = appEndo (mconcat updates <> removal) m
   in GTG m' ss
  where alienate :: s -> s -> s -> Endo (Map (s,s) (Rex a))
        alienate _1 _2 _3 = -- removing 2
          let [a, b] = map (m!) [(_1,_2), (_2,_1)]
              [c, d] = map (m!) [(_2,_3), (_3,_2)]
              [h, i] = map (m!) [(_1,_3), (_3,_1)]
              [e, f, g] = map (m!) [(_1,_1), (_2,_2), (_3,_3)]
              f' = Clos f
           in mconcat
              [ upd (_1,_1) $ e + a * f' * b
              , upd (_1,_3) $ h + a * f' * c
              , upd (_3,_1) $ i + d * f' * b
              , upd (_3,_3) $ g + d * f' * c
              ]
            where upd :: (s,s) -> Rex a -> Endo (Map (s,s) (Rex a))
                  upd pq v = Endo $ M.adjust (const v) pq

-- FIXME backward propagation for efficiency?
simplex :: Rex a -> Rex a
simplex (Alt r Nill) = simplex r
simplex (Alt Nill r) = simplex r
simplex (Alt r1 r2) = Alt (simplex r1) (simplex r2)
simplex (Cat _ Nill) = Nill
simplex (Cat Nill _) = Nill
simplex (Cat r (Prim Nothing)) = simplex r
simplex (Cat (Prim Nothing) r) = simplex r
simplex (Cat r1 r2) = Cat (simplex r1) (simplex r2)
simplex (Clos Nill) = Prim Nothing
simplex (Clos r) = Clos (simplex r)
simplex r = r

simplix :: Eq a => Rex a -> Rex a
simplix = fst . fromJust . find (uncurry (==)) . ap zip tail . iterate simplex

gtg2rex :: (Ord s, Eq a) => GTG s a -> Rex a
gtg2rex = simplix . gtg2rex'

-- Figuire 3.13
sample_dfa8 :: DFA String Int
sample_dfa8 = dfa sigma "EE" ["EO"] ["EE", "OE", "OO", "EO"] [0,1]
  where sigma "EE" 0 = "OE"
        sigma "EE" 1 = "EO"
        sigma "OE" 0 = "EE"
        sigma "OE" 1 = "OO"
        sigma "OO" 0 = "EO"
        sigma "OO" 1 = "OE"
        sigma "EO" 0 = "OO"
        sigma "EO" 1 = "EE"

-- ex 3.2-10.a
sample_nfa5 :: NFA State Int
sample_nfa5 = nfa sigma (Q 0) [Q 3] [Q 0 .. Q 3] [0,1]
  where sigma (Q 0) (Just 0) = [Q 1]
        sigma (Q 0) (Just 1) = [Q 0]
        sigma (Q 1) (Just 0) = [Q 1, Q 2]
        sigma (Q 2) (Just 0) = [Q 3]
        sigma (Q 2) (Just 1) = [Q 2]
        sigma _ _ = []

-- ex 3.2-10.b
sample_nfa6 :: NFA State Int
sample_nfa6 = nfa sigma (Q 0) [Q 0] [Q 0 .. Q 2] [0,1]
  where sigma (Q 0) (Just 0) = [Q 1]
        sigma (Q 0) (Just 1) = [Q 2]
        sigma (Q 1) (Just 0) = [Q 2]
        sigma (Q 1) (Just 1) = [Q 0]
        sigma (Q 2) (Just 1) = [Q 1]
        sigma _ _ = []

-- ex 3.2-10.c
sample_nfa7 :: NFA State Int
sample_nfa7 = nfa sigma (Q 0) [Q 1, Q 2] [Q 0 .. Q 2] [0,1]
  where sigma (Q 0) (Just 0) = [Q 0]
        sigma (Q 0) (Just 1) = [Q 1, Q 2]
        sigma (Q 1) (Just 0) = [Q 2]
        sigma (Q 2) (Just 0) = [Q 1]
        sigma _ _ = []
