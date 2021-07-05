{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS -Wno-unused-top-binds #-}
-- {-# LANGUAGE FlexibleContexts #-}

{-|
  Toy project to implement automata related proofs in haskell.
  Workflow is based on the book [An Introduction to Formal
  Languages and Automata, Fifth Edition]
  (https://dl.acm.org/doi/10.5555/1995326).

  All implementations are focused on conveying pseudo algorithms
  from the book into haskell language solely. Efficiency has never
  taken seriously, but reproducing examples in the book has.
-}

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


-- | * Handy function combinators

-- | Bi-Functor version of dot operator @('.')@.
-- | >>> (>0) .+ (+) $ -3 4
-- | True
infixr 8 .+
(.+) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.+) g f a b = g $ f a b

-- | Gets an list of orderable elements.
-- | Returns a membership checker function.
-- | It is used to convert list of state nodes
-- | into final state checker.
list2final :: Ord s => [s] -> s -> Bool
list2final ls s = S.member s $ S.fromList ls

-- | Splits a list at -2 index.
-- | >>> splitLast2 [1,2,3,4,5]
-- | ([1,2,3], [4,5])
-- | >>> splitLast2 [1]
-- | ([], [1])
splitLast2 :: [a] -> ([a], [a])
splitLast2 [] = ([],[])
splitLast2 [a] = ([],[a])
splitLast2 [a,b] = ([],[a,b])
splitLast2 (c:ab) = first (c:) $ splitLast2 ab

-- | Print dot script to stdout, so that you can
-- | use it with @dot@ cmd utility.
printDot :: PrintDot s => DotGraph s -> IO ()
printDot = LT.putStrLn . G.renderDot . toDot

-- | Present the data to user,
-- | mostly by opening xlib window.
class View d where
  view :: d -> IO ()

instance (Ord s, PrintDot s) => View (DotGraph s) where
  view dg = runGraphvizCanvas' dg Xlib


-- | * DFA (Deterministic Finite Accepter)

-- | Used to represent a DFA
data DFA
  s -- ^ how to represent a state in an automaton, they only need to be distinct to each other.
  a -- ^ alphabets the dfa accepts
  = DFA
    (s -> a -> s) -- ^ @sigma@ (σ), transition function
    s             -- ^ @initial@, the one and the only initial state
    (s -> Bool)   -- ^ @final@, checks if the state @s@ one of the final states
    (Set s)       -- ^ @states@, set of state nodes in dfa
    [a]           -- ^ @alphabets@, set of alphabets to be accepted

-- | Canonical wrapper to contruct dfa.
dfa :: Ord s
  => (s -> a -> s)  -- ^ @sigma@
  -> s              -- ^ @initial@
  -> [s]            -- ^ list of final states
  -> [s]            -- ^ list of all states
  -> [a]            -- ^ list of alphabets
  -> DFA s a
dfa si i fi st al = DFA si i (list2final fi) (S.fromList st) al


-- | Extracts transition function.
-- | @'hop' dfa s a@ returns next state to go.
-- | @'hop' dfa@ is analogous to @σ@.
hop :: DFA s a -> (s -> a -> s)
hop (DFA f _ _ _ _) = f

-- | Chained version of 'hop'.
-- | @'hops' dfa s [a1, a2...]@ is equivalent to
-- | @'hop' dfa ('hop' dfa ('hop' dfa s a1) a2) a3 ...@.
-- | @'hops' dfa@ is alanlogouse to @σ*@
hops :: DFA s a -> s -> [a] -> s
hops dfa = foldl $ hop dfa

-- | Extracts final state checker function.
-- | @'isFinal' dfa1 s@ checks if @s@ is final state of @dfa1@.
isFinal :: DFA s a -> s -> Bool
isFinal (DFA _ _ final _ _) = final

-- | Check if given @dfa@ accepts the alphabet sequence.
accepts :: DFA s a -> [a] -> Bool
accepts dfa@(DFA _ i f _ _) = f . hops dfa i


-- | ** DFA to DOT

-- | Miscellaneous class that is used to convert an automaton
-- | into graph representation. 'showAlpha' defines how given
-- | alphabet is shown on the transition edge's tag.
class ShowAlpha a where
  showAlpha :: a -> LT.Text

instance ShowAlpha Int where
  showAlpha = LT.pack . show

instance ShowAlpha Char where
  showAlpha = LT.singleton


-- | Represents states in an automaton
-- | We simply use integer-identified nodes as in the book.
newtype State = Q Int deriving (Show, Read, Eq, Ord)

-- | Implement for some canonical features,
-- | like creating a list using arithmetic sequence.
-- | e.g. @[ s1 .. s2 ]@
-- | Some functions that creates automaton from another format
-- | (s.t. regex) also depends on this feature to successively
-- | generate states. see 'Inc' and 'rex2nfa' for more.
instance Enum State where
  toEnum = Q
  fromEnum (Q x) = x

instance PrintDot State where
  unqtDot (Q n) = unqtDot $ "q" ++ show n

-- | Finds all possible edges.
-- | Helper function to graphicalize an automaton.
collectEdges :: (Ord s, Ord a)
  => (s -> a -> [s])      -- ^ @sigma@ (σ), transition function
  -> Set s                -- ^ states in the automata
  -> [a]                  -- ^ alphabets
  -> [(s,s, NonEmpty a)]  -- ^ (state_from, state_to, alphabets).
                          -- ^ Note that (state_from, state_to) is
                          -- ^ unique in returned list
collectEdges sig sts al = [ (f,t,ls) | f <- S.toList sts, (ls,t) <- deref (sprouts f) ]
  where --sprouts :: s -> [(a, [s])] -- collection of (dests, transition) from a state
        sprouts s = [ (a, sig s a) | a <- al]
        --deref :: [(a, [s])] -> [([a], s)] -- both deeply sorted
        deref = map (N.fromList . map fst &&& snd . head) . groupBy ((==) `on` snd) . sort . flatr
          -- FIXME optimize sorting
          where flatr = (uncurry (map . (,)) =<<) :: [(a,[s])] -> [(a, s)]

-- | Convert 'DFA' to DOT script. Resulting Text can be used to draw
-- | visualized graph representation of given dfa.
dfa2dot :: (Eq s, Ord s, PrintDot s, Ord a, ShowAlpha a) => DFA s a -> DotGraph s
dfa2dot dfa@(DFA sig _ _ states alphas) = DotGraph False True Nothing stms
  where
    stms = DotStmts [graphAttr, nodeAttr, edgeAttr] [] nodes edges
    nodes = map (\s -> DotNode s [nodeShape s]) $ S.toList states
    edges = map (\(f,t,ls) -> DotEdge f t [showLabel ls]) edge_pairs
    showLabel ls = textLabel . LT.intercalate "," . map showAlpha $ N.toList ls
    edge_pairs = collectEdges ((:[]) .+ sig) states alphas
    nodeShape s = shape (if isFinal dfa s then DoubleCircle else Circle)
    graphAttr = G.GraphAttrs [G.RankDir G.FromLeft, textLabel "DFA"]
    nodeAttr  = G.NodeAttrs  [G.FontSize 8.0, G.FixedSize G.SetNodeSize, G.Width 0.3]
    edgeAttr  = G.EdgeAttrs  [G.FontSize 8.0, G.ArrowSize 0.3]

instance (Eq s, Ord s, PrintDot s, Ord a, ShowAlpha a) => View (DFA s a) where
  view = view . dfa2dot

-- | ** Examples

{- | Defines DFA given in Example 2.1 of the book.
     >>> sample_dfa1 `accepts` [1,0,1]
     True
     >>> sample_dfa1 `accepts` [0,1,1,1]
     True
     >>> sample_dfa1 `accepts` [1,1,0,0,1]
     True
     >>> sample_dfa1 `accepts` [1,0,0]
     False
     >>> sample_dfa1 `accepts` [1,1,0,0]
     False
-}
sample_dfa1 :: DFA State Int
sample_dfa1 = dfa sigma (Q 0) [Q 1] [Q 0 .. Q 2] [0, 1]
  where sigma (Q 0) 0 = Q 0
        sigma (Q 0) 1 = Q 1
        sigma (Q 1) 0 = Q 0
        sigma (Q 1) 1 = Q 2
        sigma (Q 2) 0 = Q 2
        sigma (Q 2) 1 = Q 1

-- | Defines DFA given in Example 2.3 of the book.
-- | Accepts any sequence of @a@ and @b@ prefixed with @ab@.
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

-- | Defines DFA given in Example 2.4 of the book.
-- | Accepts strings not containing "001".
sample_dfa3 :: DFA String Int
sample_dfa3 = dfa sigma "0" ["λ", "0", "00"] ["λ", "0", "00", "001"] [0, 1]
  where sigma "λ"   0 = "0"
        sigma "λ"   1 = "λ"
        sigma "0"   0 = "00"
        sigma "0"   1 = "λ"
        sigma "00"  0 = "00"
        sigma "00"  1 = "001"
        sigma "001" _ = "001" -- trap!


-- | * Regular Language
-- | A language is Regular if and only if there exists a DFA that
-- | represents the language (exists M, L = L(M)).

-- Language itself is hard to represent in haskell, so we skip
-- implementing anything related to it.

-- | ** Examples

-- | Defines DFA given in Example 2.5 of the book.
-- | Accepts strings of form a[ab]*a, so that
-- | Language L = { awa: w \in {a,b}* } = L(sample_dfa4) is regular.
sample_dfa4 :: DFA State Char
sample_dfa4 = dfa sigma (Q 0) [Q 3] [Q 0 .. Q 3] ['a', 'b']
  where sigma (Q 0) 'a' = Q 2
        sigma (Q 0) 'b' = Q 1
        sigma (Q 1)  _  = Q 1 -- trap!
        sigma (Q 2) 'a' = Q 3
        sigma (Q 2) 'b' = Q 2
        sigma (Q 3) 'a' = Q 3
        sigma (Q 3) 'b' = Q 2


-- | * NFA  (Nondeterministic Finite Accepter)

-- | Used to represent a NFA
data NFA s a = NFA
  (s -> Maybe a -> Set s)
    -- ^ @sigma@ (σ), transition function. permits λ-transition
  s            -- ^ @initial@, the one and the only initial state
  (s -> Bool)  -- ^ @final@, checks if @s@ is the one of the final states
  (Set s)      -- ^ @states@, set of state nodes in dfa
  [a]          -- ^ @alphabets@, set of alphabets to be accepted

-- | Canonical wrapper to contruct nfa,
nfa :: Ord s
  => (s -> Maybe a -> [s])  -- ^ @sigma@, that returns transition candidates as list
  -> s                      -- ^ @initial@
  -> [s]                    -- ^ list of final states
  -> [s]                    -- ^ list of all states
  -> [a]                    -- ^ list of alphabets
  -> NFA s a
nfa sigma' i final' states' al = NFA sigma i final states al
  where sigma = (S.fromList .) . sigma'
        final = list2final final'
        states = S.fromList states'


-- | Extracts transition function.
-- | Analogous to 'hop' for 'DFA'
step :: NFA s a -> (s -> Maybe a -> Set s)
step (NFA f _ _ _ _) = f

-- | Extracts final state checker function.
-- | Analogous to 'isFinal' for 'DFA'
atFinal :: NFA s a -> s -> Bool
atFinal (NFA _ _ final _ _) = final

-- | Checks if given trail of transition steps on NFA is valid.
-- | Helper function for 'steps_accepted'
valid_steps :: Ord s
  => NFA s a        -- ^ nfa
  -> s              -- ^ starting state
  -> [(Maybe a, s)] -- ^ trail of transition steps.
                    -- ^ @[(a1, s1), (a2, s2) ...(an, sn)]@ means
                    -- ^ s =a1> s1 =a2> s2 ... =an> sn
  -> Bool
valid_steps nfa s ls = all (uncurry check) $ zip (s : map snd ls) ls
  where check f (a,t) = S.member t $ step nfa f a -- check from ==a=> to

{- | Checks if given trail of transition steps is valid && accepted.
     Analogous to 'isFinal' for 'DFA'.
     It also acepts empty trail in which case @initial@ should
     also be @final@ for @nfa@ to be accepted

     It requires steps trail since it is not simple at all to infer
     the right steps given only alphabe strings.
     Exhaustive searching would not work. (Imagine the process
     never halts following λ-transition cycle!)
     (Spoiler alert) This problem is resolved later in the book
     by proving NFA can be translated into DFA that represents
     same language. See 'nfa2dfa'
-}
steps_accepted :: Ord s
  => NFA s a
  -> [(Maybe a, s)] -- ^ trail of transition steps.
                    -- ^ @[(a1, s1), (a2, s2) ...(an, sn)]@ means
                    -- ^ s =a1> s1 =a2> s2 ... =an> sn
  -> Bool
steps_accepted nfa@(NFA _ initial _ _ _) steps =
  valid_steps nfa initial steps && atFinal nfa (last $ initial : map snd steps)

-- | ** NFA to DOT

instance ShowAlpha a => ShowAlpha (Maybe a) where
  showAlpha Nothing = "λ"
  showAlpha (Just a) = showAlpha a

-- | Convert 'NFA' to DOT script. Resulting Text can be used to draw
-- | visualized graph representation of given dfa.
-- |
-- | The implementation is almost identical to that of 'dfa2dot' though...
nfa2dot :: (Eq s, Ord s, PrintDot s, Ord a, ShowAlpha a) => NFA s a -> DotGraph s
nfa2dot nfa@(NFA sig _ _ states alphas) = DotGraph False True Nothing stms
  where
    stms = DotStmts [graphAttr, nodeAttr, edgeAttr] [] nodes edges
    nodes = map (\s -> DotNode s [nodeShape s]) $ S.toList states
    edges = map (\(f,t,ls) -> DotEdge f t [showLabel ls]) edge_pairs
    showLabel ls = textLabel . LT.intercalate "," . map showAlpha $ N.toList ls
    edge_pairs = collectEdges (S.toList .+ sig) states (Nothing : map Just alphas)
    nodeShape s = shape (if atFinal nfa s then DoubleCircle else Circle)
    graphAttr = G.GraphAttrs [G.RankDir G.FromLeft, textLabel "NFA"]
    nodeAttr  = G.NodeAttrs  [G.FontSize 8.0, G.FixedSize G.SetNodeSize, G.Width 0.3]
    edgeAttr  = G.EdgeAttrs  [G.FontSize 8.0, G.ArrowSize 0.3]

instance (Eq s, Ord s, PrintDot s, Ord a, ShowAlpha a) => View (NFA s a) where
  view = view . nfa2dot

-- | ** Examples

-- | Defines DFA given in Example 2.7 of the book.
sample_nfa1 :: NFA State Char
sample_nfa1 = nfa sigma (Q 0) [Q 3, Q 5] [Q 0 .. Q 5] ['a']
  where sigma (Q 0) (Just 'a') = [Q 1, Q 4]
        sigma (Q 1) (Just 'a') = [Q 2]
        sigma (Q 2) (Just 'a') = [Q 3]
        sigma (Q 4) (Just 'a') = [Q 5]
        sigma (Q 5) (Just 'a') = [Q 4]
        sigma _ _ = []
        -- NOTE hopping haskell optimize it & compute in compile time

{- | Defines DFA given in Example 2.8 of the book.
     >>> steps_accepted sample_nfa2 [ -- 1010
     ...   (1, Q 1), (0, Q 0), (1, Q 1), (0, Q 0),
     ... ]
     True
     >>> steps_accepted sample_nfa2 [ -- 101010
     ...   (1, Q 1), (0, Q 0), (1, Q 1), (0, Q 0), (1, Q 1), (0, Q 0),
     ... ]
     True
     >>> steps_accepted sample_nfa2 [ -- 110
     ...   (1, Q 1), (1, Q 1), (0, Q 0),
     ... ]
     False
     >>> steps_accepted sample_nfa2 [ -- 10100
     ...   (1, Q 1), (0, Q 0), (1, Q 1), (0, Q 0), (0, Q 0),
     ... ]
     False
-}
sample_nfa2 :: NFA State Int
sample_nfa2 = nfa sigma (Q 0) [Q 0] [Q 0 .. Q 2] [0, 1]
  where sigma (Q 0) Nothing  = [Q 2]
        sigma (Q 0) (Just 1) = [Q 1]
        sigma (Q 1) (Just 0) = [Q 0, Q 2]
        sigma (Q 1) (Just 1) = [Q 2]
        sigma _ _ = []


-- | ** NFA == DFA

-- | *** NFA => DFA

-- | Converts 'NFA' to 'DFA'. It's actually simple as wrapping sigma
-- | to return singleton set.
dfa2nfa :: Ord s => DFA s a -> NFA s a
dfa2nfa (DFA f initial final states alphas) = NFA f' initial final states alphas
  where f' s mx = S.fromList . maybeToList $ f s <$> mx


-- | *** NFA <= DFA

-- | Given a directed graph defined by transition function,
-- | collect all reachable nodes from a starting node by
-- | Breadth First Search.
-- | Handy helper function.
bfs :: Ord s
  => (s -> Set s) -- ^ transition function
  -> s            -- ^ starting node
  -> Set s
bfs f = bfs' f . S.singleton

-- | Given a directed graph defined by transition function,
-- | collect all reachable nodes from a set of nodes by
-- | Breadth First Search.
bfs' :: Ord s
  => (s -> Set s) -- ^ transition function
  -> Set s        -- ^ starting set
  -> Set s
bfs' f = bfs'' f S.empty
  where
    bfs'' f ret ss
      | S.null ss = ret
      | otherwise =
        let (s, ss') = S.deleteFindMin ss
        in if s `S.member` ret then bfs'' f ret ss' -- s already seen, ignore it
           else bfs'' f (S.insert s ret) (ss `S.union` f s)


-- | Translation of pseudo algorithm in Theorem 2.2 from the book.
-- | Does not remove unreachable states (it just sets
-- | @dfa_state = powerSet nfa_state@). See 'removeInac' to
-- | trim them out.
nfa2dfa :: forall s a. (Ord s, Ord a) => NFA s a -> DFA (Set s) a
nfa2dfa (NFA f initial final states alphas) = DFA f' initial' final' states' alphas
  where f' :: Set s -> a -> Set s
        f' ss a = foldMap (\s -> extend_lambda . f s . Just $ a) . extend_lambda $ ss
        -- foldmap uses mconcat to fold. monoid (semigroup) operation of Set is Union
          where extend_lambda :: Set s -> Set s
                extend_lambda = bfs' (\s -> f s Nothing)
        initial' = S.singleton initial
        final' ss = any final $ S.toList ss
        -- NOTE S.toList works as iterator for a set (due to lazyness)
        -- FIXME No, it doesn't list is created from inner-most, while accessed outer-most.
        -- construction of head of the list is break point
        states' = S.powerSet states

-- | *** Examples

instance PrintDot a => PrintDot (Set a) where
  unqtDot ss | S.null ss = unqtDot ("∅" :: LT.Text)
             | otherwise = G.addQuotes "'" . go $ ss
    where go = G.hcat . G.punctuate G.comma . sequenceA . map G.unqtDot . S.toAscList

-- | Example 2.12
-- | @view sample_nfa3@ yields Figure 2.12 in the Book.
-- | @view . removeInac $ sample_nfa3@ yields
-- | Figure 2.13 in the Book.
sample_nfa3 :: NFA State Char
sample_nfa3 = nfa sigma (Q 0) [Q 1] [Q 0 .. Q 2] ['a', 'b']
  where sigma (Q 0) (Just 'a') = [Q 1]
        sigma (Q 1) (Just 'a') = [Q 1]
        sigma (Q 1) Nothing    = [Q 2]
        sigma (Q 2) (Just 'b') = [Q 0]
        sigma _ _ = []

-- | Example 2.13
-- | @view sample_nfa4@ yields Figure 2.14 in the Book.
-- | @view . removeInac $ sample_nfa4@ yields
-- | Figure 2.16 in the Book.
sample_nfa4 :: NFA State Int
sample_nfa4 = nfa sigma (Q 0) [Q 1] [Q 0 .. Q 2] [0, 1]
  where sigma (Q 0) (Just 0) = [Q 0, Q 1]
        sigma (Q 0) (Just 1) = [Q 1]
        sigma (Q 1) (Just _) = [Q 2]
        sigma (Q 2) (Just 1) = [Q 2]
        sigma _ _ = []

-- | Remove inaccessible state nodes from the DFA's state set.
-- | It performs 'bfa' from @initial@ then replace the state set
-- | with the result.
removeInac :: Ord s => DFA s a -> DFA s a
removeInac (DFA si i fi _ als) = DFA si i fi accessibles als
  where accessibles = bfs (\s -> S.fromList $ map (si s) als) i


-- | * Reduction

-- | ** Helpers

-- | Boolean XOR operator.
xor :: Bool -> Bool -> Bool
xor x y = not x && y || x && not y

-- | Creates an sorted tuple.
-- | >>> 1 𒑰 2
-- | (1,2)
-- | >>> 2 𒑰 1
-- | (1,2)
infix 8 𒑰
( 𒑰) :: Ord a => a -> a -> (a,a)
(𒑰) = \x y -> if x < y then (x,y) else (y,x)


-- | ** Implementation

-- | Translation of pseudo algorithm mark
-- | used in Theorem 2.3 from the book.
mark :: forall s a. (Ord s, Ord a) => DFA s a -> (s -> s -> Bool)
mark (DFA sig _ final sts alphas) p q =
  let distinguishables = rec sts_seed :: Set (s,s)
   in (p 𒑰 q) `S.member` distinguishables
  where
    rec dist =
      let sts_new = expand dist
       in if null sts_new then dist
          else rec $ dist `S.union` sts_new
    expand dist = sts2 `S.difference` dist & S.filter (\(p,q) ->
      any (\a -> (sig p a 𒑰 sig q a) `S.member` dist) alphas)
    sts_seed = S.filter (\(p,q) -> final p `xor` final q) sts2
    sts2 = S.filter (\(p,q) -> p<q) $ S.cartesianProduct sts sts

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

{-
  Consider the procedure of mark from the book.
  Step 1 removed unaccessible states (we already implemented the
  functionality with separate function 'removeInac').
  Step 2 prepares basic set of distinguishable pairs (let's call it seeds).
  Step 3 expands the seeds repeatedly till no more distinguishable
  pairs are found.

  If you think about it, for each iteration of step 3, discovering
  a new pair of distinguishable states @(p,q)@ only occurs when
  @(sig p a, sig q a)@, for some @a@, is a pair of distinguishable
  states that is newly discovered at previous iteration.
  For example, suppose @(1,2)@ and @(3,4)@ are found to be
  distinguishable pairs at 2nd and 3rd iteration of step 2 respectively.
  Then at the 4th iteration, any distinguishable pair found, say
  @(p,q)@, satisfies @(sig p a, sig q a) = (3,4)@ for some @a@,
  but never @(sig p b, sig q b) = (1,2)@ with any @b@.
  If there were such @b@, @(p,q)@ should have found at 3rd
  iteration along with @(3,4). But it didn't, indeed there is no
  such @b@.

  I might rephrase it as "new discoveries only happens at the border",
  where the border stands for set of pairs that are found distinguishable
  during the iteration right before.

-}

{-
  Discovering new distinguishable pairs strictly depends on the pairs
  that are already discovered.
  It's already graph traversal scheme. no need to concern where the
  new discovery occures. we could use dfs to collect distinguishable
  pairs instead.
-}

-- | Implementation of pseudo algorithm mark
-- | that uses bfs from the bottom of distinguishable chain.
-- |
-- | Distinguishability propagates from the @seeds@ (Set of pair of
-- | states that is prepared during step 2) by simultaneous state
-- | transition (@ssig (p,q) a = (sig p a, sig q a)@). Consider this
-- | as a directed graph where edges are inverse of @ssig@ and
-- | nodes are pair of states. We can just traverse the graph to find
-- | all distinguishable pairs. 'mark_bfs' is the version
-- | that uses bfs scheme starting with @seeds@.
mark_bfs :: (Ord s, Ord a) => DFA s a -> (s -> s -> Bool)
mark_bfs (DFA sig _ final states alphas) p q =
  let distinguishables = bfs' propagate seeds
   in (p 𒑰 q) `S.member` distinguishables
  where
    -- propagates to next distinguishable pairs
    propagate (p,q) = S.fromList [ (p' 𒑰 q') |
      a <- alphas, p' <- gis p a, q' <- gis q a, p' /= q']
    -- strict UR half of sorted sts * sorted sts, filterd by xor-final
    seeds = S.fromList [ (p 𒑰 q) |
      p <- sts, q <- sts, p /= q, final p `xor` final q]
    -- inverse of sig (sig :: s -> a -> s; gis :: s -> a -> [s])
    gis = let maps = [((sig s a, a), [s]) | s <- sts, a <- alphas]
              memo = foldl (flip.uncurry $ M.insertWith (++)) M.empty maps
           in curry $ flip (M.findWithDefault []) memo
    sts = S.toList states


-- | Translation of pseudo algorithm reduce
-- | used in Theorem 2.4 from the book.
reduceIndist :: (Ord s, Ord a) => DFA s a -> DFA (Set s) a
reduceIndist dfa@(DFA sig init fin states al) =
  let sig' ss a = lift . (flip sig a) . sink $ ss
      (init', fin') = (lift init, fin . sink)
      states' = S.fromList $ map (bfs lift) $ S.toList states
   in DFA sig' init' fin' states' al
  where sink ss = S.findMin ss
        lift p = S.filter (isIndist p) states
        isIndist p q = not $ marked p q
        marked = mark_bfs dfa

-- | ** Examples
dfa' :: Ord a => [((Int, a), Int)] -> Int -> [Int] -> [Int] -> [a] -> DFA State a
dfa' tbl i fi st al = dfa sigma (Q i) (map Q fi) (map Q st) al
  where sigma = curry $ Q <<< (M.fromList tbl !) <<< first (\(Q n) -> n)

-- | Example 2.14
sample_dfa5 :: DFA State Int
sample_dfa5 = dfa' tbl 0 [3, 4] [0 .. 5] [0, 1]
  where tbl = [ ((0,0), 1), ((0,1), 2), ((1,0), 2), ((1,1), 3)
              , ((2,0), 2), ((2,1), 4), ((3,0), 3), ((3,1), 3)
              , ((4,0), 4), ((4,1), 4), ((5,0), 5), ((5,1), 4) ]

-- | Example 2.15
sample_dfa6 :: DFA State Int
sample_dfa6 = dfa' tbl 0 [2, 4] [0 .. 4] [0, 1]
  where tbl = [ ((0,0), 1), ((0,1), 3), ((1,0), 2), ((1,1), 4)
              , ((2,0), 1), ((2,1), 4), ((3,0), 2), ((3,1), 4)
              , ((4,0), 4), ((4,1), 4) ]

-- | DFA that is quite large. Wouldn't see @reduceIndist sample_dfa7@
-- | done unless we optimize our implementation.
sample_dfa7 :: DFA State Int
sample_dfa7 = dfa sigma (Q 0) [Q 1] [Q 0 .. Q 25] [0, 1, 2]
  where sigma (Q n) a = Q . (`mod` 26) . fibo . (+ a) $ n
        fibo 0 = 1
        fibo 1 = 1
        fibo n = fibo (n-1) + fibo (n-2)


-- | ** Boost helpers
-- | Attemps to optimize DFA

-- | Makes sigma produce fater using memoization
quicker :: (Ord s, Ord a) => DFA s a -> DFA s a
quicker (DFA sigma i final states alphas) = DFA sigma' i final' states alphas
  where sigma' = curry (M.fromSet (uncurry sigma) inputs !)
        inputs = S.fromList [(s,a) | a <- alphas, s <- S.toList states]
        final' = (M.fromSet final states !)

-- | Rename the states in case you want to.
rename :: forall t s a. (Ord t, Ord s) => Set t -> DFA s a -> DFA t a
rename states' (DFA sigma init fin states al) = DFA sigma' init' fin' states' al
  where conv = flip S.elemAt states' . flip S.findIndex states :: s -> t
        conv' = flip S.elemAt states . flip S.findIndex states' :: t -> s
        sigma' = flip (\a -> conv . flip sigma a . conv')
        init' = conv init
        fin' = fin . conv'


-- | * Regex

-- | ** Helpers

-- | Used to generate state ids succesively while
-- | constructing 'NFA'.
type Inc n = ST.State n

-- | Returns next available state id.
next :: Enum n => Inc n n
next = ST.get >>= \n -> ST.modify succ >> return n

-- | Synonym for 'ST.runState'
runInc :: Inc n a -> n -> (a, n)
runInc = ST.runState


-- | Used to support imcreamental construction of non-diterministic σ
-- | transition function. To implement 'Semigroup' and 'Monoid' on σ.
newtype SigBuilder s a = SigBuilder { build :: s -> Maybe a -> Set s }

-- | @wire i ma f sb@ appends new transition rule i =ma=> f to 'Sigbuilder' @sb.
-- | In other words, it draws new transition edge in the diagram of @sb@.
wire :: (Ord s, Eq a) => s -> Maybe a -> s -> SigBuilder s a -> SigBuilder s a
wire init malpha fin sb = SigBuilder $ \s ma ->
  if s == init && ma == malpha then fin `S.insert` build sb s ma
  else build sb s ma

-- | Semigroup operator unifies two Sigbuilter.
-- | Diagram of unified σ contains all the transition edges
-- | (and states) in both input σ.
instance Ord s => Semigroup (SigBuilder s a) where
  sb1 <> sb2 = SigBuilder $ \s ma ->
    build sb1 s ma `S.union` build sb2 s ma

-- | Empty 'Sigbuilder' defines automaton that
-- | does not transit whatsoever. σ always returns 'S.Empty'.
instance Ord s => Monoid (SigBuilder s a) where
  mempty = SigBuilder $ const (const S.empty)


-- | Simplified version of 'NFA'. Only holds σ, initial
-- | and single final state. To be used while generating
-- | NFA increamentally.
data NFA' s a = NFA' (SigBuilder s a) s s


-- | ** Rex

-- | ADT represents regular expression.
-- | 'Rex' is strict in its argument to force finite structure.
-- | (since the book stipulates it to be finite)
data Rex a
  = Nill -- ^ ∅
  | Prim !(Maybe a) -- ^ Primitive Regular Expressions.
                    -- ^ @Nothing@ for λ, @Just a@ for alphabet a
  | Alt !(Rex a) !(Rex a) -- ^ r1 + r2
  | Cat !(Rex a) !(Rex a) -- ^ r1 ⋅ r2
  | Clos !(Rex a)         -- ^ r1 *
  deriving (Show, Read, Eq)

-- | Num instance implementation only to utilize operators.
-- | Got the idea from <http://hackage.haskell.org/package/algebraic-graphs-0.4/docs/Algebra-Graph.html#t:Graph>
instance Num (Rex a) where
  (+) = Alt
  (*) = Cat
  abs = undefined
  signum = undefined
  fromInteger 0 = Nill
  fromInteger _ = undefined
  negate = undefined

-- | Handy helper for primitive. Synonym for @Prim Nothing@
λ :: Rex a
λ = Prim Nothing

-- | Handy helper for primitive. Synonym for @Prim . Just@
ε :: a -> Rex a
ε = Prim . Just

-- | Treat 'Rex' as alphabet, to use it as transition edge.
-- | Used with Generalized Transition Graph ('GTG')
-- | Convenient when converting 'Rex' ADT into string form.
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

instance ShowAlpha a => View (Rex a) where
  view = LT.putStr . go "" where
    go s (Nill)         = l s $ prim "∅"
    go s (Prim Nothing) = l s $ prim "λ"
    go s (Prim (Just a)) = l s . prim $ showAlpha a
    go s (Alt r1 r2) =
      let l1 = go (s+++"L ") r1
          l2 = go (s+++"R ") r2
          mid = "-------------"
       in l1 +++ l s mid +++ l2
    go s (Cat r1 r2) = go s r1 +++ go s r2
    go s (Clos r) = go (s +++ "| ") r
    l s x = s +++ x +++ "\n"
    prim x = "\x1b[33m" +++ x +++ "\x1b[0m"
    (+++) = LT.append


-- | Example 3.7 a->0; b->1;
-- | showAlpha sample_rex1 == "(0+11)*(10*+λ)"
sample_rex1 :: Rex Int
sample_rex1 = (Clos $ ε 0 + ε 1 * ε 1) * (ε 1 * Clos (ε 0) + λ)


-- | *** Rex => NFA

-- | Converts 'Rex' to 'NFA' following the Theorem 3.1 in the book.
-- | Nevertheless, @rex2nfa sample_rex1@ does not yield the
-- | diagram in Figure 3.7 but more verbose with redundant
-- | λ-transitions.
rex2nfa :: Ord a => Rex a -> NFA State a
rex2nfa rex =
  let (NFA' sig init fin, q) = runInc (rex2nfa' rex) (Q 0)
      states = S.fromList [Q 0 .. pred q]
      alphabets = S.toList $ rex2alphas rex
   in NFA (build sig) init (==fin) states alphabets

-- | Extract alphabet-only sequence from given rex.
-- | Conceptually, it is just showAlpha & filter alphabet.
rex2alphas :: Ord a => Rex a -> Set a
rex2alphas (Prim (Just a)) = S.singleton a
rex2alphas (Alt nl nr) = (S.union `on` rex2alphas) nl nr
rex2alphas (Cat nl nr) = (S.union `on` rex2alphas) nl nr
rex2alphas (Clos na) = rex2alphas na
rex2alphas _ = S.empty

-- | Core implementation of 'rex2nfa'.
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
  (init, fin) <- (,) <$> next <*> next
  NFA' sig' init' fin' <- rex2nfa' na
  let sig = sig'
            & wire init Nothing fin
            & wire init Nothing init'
            & wire fin' Nothing fin
            & wire fin Nothing init
  return $ NFA' sig init fin

-- | Attempt to gnerate more simpler nfa.
-- | (by omitting redundant λ-transitions.. etc)
-- | But failed.
-- | Validity is not guaranteed.
rex2nfa_simpler :: Ord a => Rex a -> NFA State a
rex2nfa_simpler rex =
  let (sig, q) = runInc (rex2nfa'' rex (Q 0) (Q 1)) (Q 2)
      states = S.fromList [Q 0 .. pred q]
      alphabets = S.toList $ rex2alphas rex
   in NFA (build sig) (Q 0) (== Q 1) states alphabets

-- | Core implementation of 'rex2nfa_simpler'.
rex2nfa'' :: (Enum s, Ord s, Eq a) => Rex a -> s -> s -> Inc s (SigBuilder s a)
rex2nfa'' Nill _ _ = return mempty
rex2nfa'' (Prim ma) i f = return $ mempty & wire i ma f
rex2nfa'' (Alt nl nr) i f = do
--  (i1, i2, f1, f2) <- (,,,) <$> next <*> next <*> next <*> next
--  sigl <- rex2nfa'' nl i1 f1
--  sigr <- rex2nfa'' nr i2 f2
--  return $ sigl <> sigr
--           & wire i Nothing i1
--           & wire i Nothing i2
--           & wire f1 Nothing f
--           & wire f2 Nothing f
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
           & wire i Nothing f
           & wire i Nothing init
           & wire fin Nothing f
           & wire f Nothing i
-- FIXME it is neither smallest nor correct


-- | **** Examples

-- | Example 3.8
-- | >>> LT.putStrLn $ showAlpha sample_rex2
-- | a*+a*(a+b)c*
sample_rex2 :: Rex Char
sample_rex2 = (Clos $ ε 'a') + (Clos $ ε 'a') * (ε 'a' + ε 'b') * (Clos $ ε 'c')


-- | *** NFA => REX


-- (complete) Generalized Transfer Graph
-- keeps track of all the nodes (states) in the graph
-- where [fin, init] is the last elem
data GTG s a = GTG
  { getRexMap :: Map (s,s) (Rex a)
  , getStates :: [s]
  } deriving (Show, Read, Eq)

-- | A NFA with exactly one final state. Used while converting
-- | 'NFA' to 'GTG'
data MonofinNFA s a = MonofinNFA
  (s -> Maybe a -> Set s)
    -- ^ @sigma@ (σ), transition function. permits λ-transition
  s            -- ^ @initial@, the one and the only initial state
  s            -- ^ @final@, the one and the only final state
  (Set s)      -- ^ @states@, set of state nodes in dfa
  [a]          -- ^ @alphabets@, set of alphabets to be accepted

-- | Convert any 'NFA' into 'MonofinNFA' by adding new genuine
-- | final state and edges redirected from old (disqualified)
-- | final states.
monofinNFA :: (Enum s, Ord s, Eq a) => NFA s a -> MonofinNFA s a
monofinNFA (NFA sig ini final states al) =
  let fin' = succ $ S.findMax states -- cannot fail, states never empty (it must include initial)
      fins = filter final $ S.toList states
      wires = map (\f -> Endo $ wire f Nothing fin') fins -- isn't it sub-optimal? `if s `elem` fins -> fin' ???
      sig' = build . appEndo (mconcat wires) $ SigBuilder sig
      states' = fin' `S.insert` states
   in case fins of
        [f] | f /= ini -> MonofinNFA sig ini f states al
        _ -> MonofinNFA sig' ini fin' states' al

-- | Convert any 'NFA' into 'GTG'.
nfa2gtg :: (Enum s, Ord s, Ord a) => NFA s a -> GTG s a
nfa2gtg nfa =
  let MonofinNFA sig ini fin states alphas = monofinNFA nfa
      edge_pairs = collectEdges (S.toList .+ sig) states (Nothing : map Just alphas)
      partial = foldl (\m (f,t,ls) -> M.insert (f,t) (as2r ls) m) M.empty edge_pairs
      full = foldl insertDummy partial [(p,q) | p <- S.toList states, q <- S.toList states ]
      states' = S.toList . S.delete fin . S.delete ini $ states
   in GTG full $ states' ++ [ini, fin] -- make sure initial and final being last 2 elem
   -- FIXME should we just have set of all states and keep initial and final states in constructor separately?
  where as2r (a:|[]) = Prim a -- [Alphabet] -> balanced Regex Alt tree, with Prim leaves
        as2r as = let (ls, rs) = halve as in (Alt `on` as2r) ls rs
        halve xs = -- halve assumes `length xs >= 2`
          let n = (length xs) `div` 2
           in (N.fromList $ N.take n xs, N.fromList $ N.drop n xs)
        insertDummy m pq = M.insertWith (flip const) pq Nill m
        -- FIXME should we actually insert it? can't just find with default when utilizing?

-- | Convert 'GTG' to DOT script. Resulting Text can be used to draw
-- | visualized graph representation of given dfa.
gtg2dot :: (PrintDot s, ShowAlpha a) => GTG s a -> DotGraph s
gtg2dot (GTG m ss) = DotGraph False True Nothing stms
  where
    stms = DotStmts [graphAttr, nodeAttr, edgeAttr] [] nodes edges
    nodes = uncurry (++) <<< circle *** dcircle <<< init &&& (:[]) . last $ ss
      where circle  = map $ flip DotNode [shape Circle]
            dcircle = map $ flip DotNode [shape DoubleCircle]
    edges = map (\((f,t),r) -> DotEdge f t [textLabel $ showAlpha r]) $ M.toList m
    graphAttr = G.GraphAttrs [G.RankDir G.FromLeft, textLabel "GTG"]
    nodeAttr  = G.NodeAttrs  [G.FontSize 8.0, G.FixedSize G.SetNodeSize, G.Width 0.3]
    edgeAttr  = G.EdgeAttrs  [G.FontSize 8.0, G.ArrowSize 0.3]

instance (ShowAlpha a, Ord s, PrintDot s) => View (GTG s a) where
  view = view . gtg2dot

-- | Convert any 'NFA' into unsimplified 'GTG'.
-- | Partial implementation of pseudo algorithm
-- | nfa-to-rex from the book.
gtg2rex' :: Ord s => GTG s a -> Rex a
gtg2rex' gtg@(GTG m states) = case states of
  -- DFA/NFA has at least 1 state (initial)
  -- GTG has at least 2 states (initial, monofin)
  [ini, fin] -> -- step 3
    let r1 = m ! (ini, ini)
        r2 = m ! (ini, fin)
        r3 = m ! (fin, ini)
        r4 = m ! (fin, fin)
        r1' = Clos r1
     in r1' * r2 * Clos (r4 + r3 * r1' * r2)
  _ -> gtg2rex' . reduceGTG $ gtg -- step 4

-- | Core mechanics of 'gtg2rex'. Covers cases when
-- | there are move than 2 states in 'GTG'
-- | Edge simplification is done with other function 'simplex'.
reduceGTG :: forall s a. Ord s => GTG s a -> GTG s a
reduceGTG (GTG m (s:ss)) =
  let withS (p,q) = p == s || q == s
      updates = [alienate p s q | p <- ss, q <- ss, p /= q]
      removal = Endo $ M.filterWithKey (const . not . withS)
      m' = appEndo (mconcat updates <> removal) m
   in GTG m' ss
  where -- generate GTG edges to so that _2 can be removed
        alienate :: s -> s -> s -> Endo (Map (s,s) (Rex a))
        alienate _1 _2 _3 =
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

-- | Simplify given regex. as the step 5 in rex-to-nfa suggests.
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
simplex r = r -- primitives

-- | Repeatedly apply 'simplex' till there's no more simplification.
-- FIXME backward propagation for efficiency?
simplix :: Eq a => Rex a -> Rex a
simplix = fst . fromJust . find (uncurry (==)) . ap zip tail . iterate simplex

-- | Convert any 'NFA' into 'GTG'.
-- | Implementation of pseudo algorithm nfa-to-rex from the book.
-- |
-- | It's simply @simplix . gtg2rex'@.
gtg2rex :: (Ord s, Eq a) => GTG s a -> Rex a
gtg2rex = simplix . gtg2rex'

-- | Simple abbreviation. @nfa2rex =  gtg2rex . nfa2gtg@.
nfa2rex :: (Ord s, Enum s, Ord a, Eq a) => NFA s a -> Rex a
nfa2rex = gtg2rex . nfa2gtg


-- | **** Examples

{- |
  FIXME 'sample_dfa8' uses String as state id,
  which is not 'Enum' instance. But 'monofinNFA' (so as 'nfa2gtg')
  requires it to be Enum instance to add a new ultimate-final state.
  sample_dfa8 already has single final state so that no new state
  will be introduced. So, this is workaround to pass typecheck.
  trying to call 'monofinNFA' or 'nfa2gtg' with a dfa/nfa having a list type
  as state id and multiple final states would result in undefined.
  Luckily, no such thing in following example.
-}
instance forall a. Enum [a] where
  toEnum = undefined
  fromEnum = undefined


-- | Example 3.11
-- | >>> let dfa = nfa2dfa . rex2nfa . gtg2rex . nfa2gtg . dfa2nfa $ sample_dfa8
-- | >>> accepts dfa [1]
-- | True
-- | >>> accepts dfa [1,0,1]
-- | False
-- | >>> accepts dfa [1,1,0,0,1]
-- | True
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

-- Exercise 3.2-10.a
sample_nfa5 :: NFA State Int
sample_nfa5 = nfa sigma (Q 0) [Q 3] [Q 0 .. Q 3] [0,1]
  where sigma (Q 0) (Just 0) = [Q 1]
        sigma (Q 0) (Just 1) = [Q 0]
        sigma (Q 1) (Just 0) = [Q 1, Q 2]
        sigma (Q 2) (Just 0) = [Q 3]
        sigma (Q 2) (Just 1) = [Q 2]
        sigma _ _ = []

-- Exercise 3.2-10.b
sample_nfa6 :: NFA State Int
sample_nfa6 = nfa sigma (Q 0) [Q 0] [Q 0 .. Q 2] [0,1]
  where sigma (Q 0) (Just 0) = [Q 1]
        sigma (Q 0) (Just 1) = [Q 2]
        sigma (Q 1) (Just 0) = [Q 2]
        sigma (Q 1) (Just 1) = [Q 0]
        sigma (Q 2) (Just 1) = [Q 1]
        sigma _ _ = []

-- Exercise 3.2-10.c
sample_nfa7 :: NFA State Int
sample_nfa7 = nfa sigma (Q 0) [Q 1, Q 2] [Q 0 .. Q 2] [0,1]
  where sigma (Q 0) (Just 0) = [Q 0]
        sigma (Q 0) (Just 1) = [Q 1, Q 2]
        sigma (Q 1) (Just 0) = [Q 2]
        sigma (Q 2) (Just 0) = [Q 1]
        sigma _ _ = []

data Linear v a = Linear [a] (Maybe v) [a] deriving (Show, Read, Eq)
newtype LinearL v a = LinearL (Linear v a) deriving (Show, Read, Eq)
newtype LinearR v a = LinearR (Linear v a) deriving (Show, Read, Eq)
data Regular v a = RegularL (LinearL v a) | RegularR (LinearR v a)
  deriving (Show, Read, Eq)

getLinearL :: Linear v a -> Maybe (LinearL v a)
getLinearL p@(Linear [] _ _) = Just $ LinearL p
getLinearL _ = Nothing

getLinearR :: Linear v a -> Maybe (LinearR v a)
getLinearR p@(Linear _ _ []) = Just $ LinearR p
getLinearR _ = Nothing

getRegular :: Linear v a -> Maybe (Regular v a)
getRegular p = RegularL <$> getLinearL p <|> RegularR <$> getLinearR p


--data LinearG v a = LiearG (v -> l v a) v (Set v) [a]
