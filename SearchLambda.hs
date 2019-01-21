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
