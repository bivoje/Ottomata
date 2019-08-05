{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Function (on)
import Data.List (find, groupBy, sort)
import Data.Maybe (isJust)
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.IO as LT
import Data.GraphViz
import Data.GraphViz.Printing (renderDot)
import Control.Arrow

data DFA s a = DFA
  { hop   :: s -> a -> s
  , initial :: s
  , final   :: [s]
  }

hops :: DFA s a -> s -> [a] -> s
hops dfa = foldl $ hop dfa

hopping :: DFA s a -> [a] -> s
hopping dfa = hops dfa (initial dfa)

isFinal :: Eq s => DFA s a -> s -> Bool
isFinal dfa s = isJust . find (== s) $ final dfa

runDFA :: Eq s => DFA s a -> [a] -> Bool
runDFA dfa = isFinal dfa . hopping dfa


class ShowAlpha a where
  showAlpha :: a -> LT.Text

instance ShowAlpha Int where
  showAlpha n = LT.pack $ show n

dfa2dot :: (Eq s, Ord s, PrintDot s, Ord a, ShowAlpha a) => DFA s a -> [s] -> [a] -> LT.Text
dfa2dot dfa states alphas = renderDot . toDot . DotGraph False True Nothing $ stms
  where
    stms = DotStmts [] [] nodes edges
    nodes = map (\s -> DotNode s $ nodeAttr s) states
    nodeAttr s = if isFinal dfa s then [shape DoubleCircle] else [shape Circle]
    edges = concat $ map (\(f,tls) -> map (\(t,ls) -> DotEdge f t [showLabel ls]) tls) edge_pairs
    showLabel ls = textLabel . LT.intercalate "," $ map showAlpha ls
    edge_pairs = [ (s,) $ collect [ (hop dfa s a, a) | a <- alphas] | s <- states ]
    collect = map (fst . head &&& map snd) . groupBy ((==) `on` fst) . sort

newtype State = Q Int deriving (Show, Read, Eq, Ord)

instance PrintDot State where
  unqtDot (Q n) = unqtDot $ "q" ++ show n

sample_dfa :: DFA State Int
sample_dfa = DFA sigma (Q 0) [Q 1]
  where sigma (Q 0) 0 = Q 0
        sigma (Q 0) 1 = Q 1
        sigma (Q 1) 0 = Q 0
        sigma (Q 1) 1 = Q 2
        sigma (Q 2) 0 = Q 2
        sigma (Q 2) 1 = Q 1

sample_dfa_dot :: LT.Text
sample_dfa_dot = dfa2dot sample_dfa [Q 0, Q 1, Q 2] [0, 1]