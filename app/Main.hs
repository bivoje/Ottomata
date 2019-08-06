{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Function (on)
import Data.List (find, groupBy, sort)
import Data.Maybe (isJust, maybeToList)
import Data.Set (Set, (\\))
import qualified Data.Set as S
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
