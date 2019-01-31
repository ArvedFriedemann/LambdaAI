module SearchLambda where

import LambdaCompiler
import Data.List
import Control.Monad.Trans.State.Lazy
import Debug.Trace
import Data.Text.Lazy (toStrict)
import Text.Pretty.Simple
import TextShow.Debug.Trace

type VarMon a b = State [a] b

next::VarMon a a
next = state (\x -> (head x, tail x))

--vars, current bond variables, "empty" symbol, current term
nextLambda::(Eq a) => [a] -> a -> Lambda a -> [Lambda a]
nextLambda stack e (Variable _) =  (Variable <$> stack)++[Abstraction e x | x <- (Variable <$> (e:stack))]
nextLambda stack e (Abstraction x y) = [Abstraction x z | z <- nextLambda (x:stack) e y] ++
                                        (nextLambda stack e (Application (Variable e) (Variable e)))
nextLambda stack e (Application a b) = [Application x y | x <- nextLambda stack e a, y <- nextLambda stack e b]

--previous
nextLambdas::(Show a, Enum a, Eq a) => [Lambda a] -> a ->  Lambda a -> [[Lambda a]]
nextLambdas prev e cl = nextList : (concat $ transpose $ (nextLambdas (nextList++prev) e) <$> (nextList))
  where nextList = nub (((renameDubs succ) <$> (nextLambda [] e cl)) \\ (cl:prev))

lambdas::(Show a, Enum a, Eq a) => a -> [[Lambda a]]
lambdas o =  (nextLambdas [] o (Variable o))

l_id::Lambda Integer
l_id = lsa "/1 1"
l_true::Lambda Integer
l_true = lsa "/2/1 2"
l_false::Lambda Integer
l_false = lsa "/2/1 1"
l_tuple::Lambda Integer
l_tuple = lsa "/3/2/1 1 3 2"
l_fst::Lambda Integer
l_fst = lsa "/3 3 (/2/1 2)"
l_snd::Lambda Integer
l_snd = lsa "/3 3 (/2/1 1)"
l_zero::Lambda Integer
l_zero = lsa "/1 /2 2"
l_succ::Lambda Integer
l_succ = lsa "/1/2/3 2(1 2 3)"

--TODO: something doesn't work for higher numbers (starts at: l_tuple<>l_true<>(l_tuple <> l_true <> l_false))
curchnum::Int -> Lambda Integer
curchnum i = runLambda succ $ foldr (\a b -> l_tuple <> l_id <> b) l_false (replicate i l_id)

{-
lambdaToLambda'::a -> a -> a -> Lambda Int -> Lambda Int
lambdaToLambda' var abst appl (Variable x) =

searchCompiler::Int -> [Lambda a]
searchCompiler = []
-}
