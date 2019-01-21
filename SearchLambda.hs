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

--current bond variables
nextLambda::(Eq a) => [a] -> Lambda a -> VarMon a [Lambda a]
nextLambda stack (Variable _) =  (\v -> [Abstraction v (Variable y) | y <- v:stack]) <$> next
nextLambda stack (Abstraction x y) = do {
                                        direct <- nextLambda (x:stack) y;
                                        return $ [Abstraction x z | z <- direct]
                                              ++ [Abstraction x $ Application (Variable x) (Variable x)]
                                      }
nextLambda stack (Application a b) = do {
                                        xs <- nextLambda stack a;
                                        ys <- nextLambda stack b;
                                        return [Application x y | x <- xs, y <- ys]
                                      }
nextLambdas::(Show a, Enum a, Eq a) => [a] -> Lambda a -> VarMon a [Lambda a]
nextLambdas stack cl = do {
  l <- (\\ [cl]) <$> nextLambda stack cl;
  ls <- sequence $ (nextLambdas stack) <$> l;
  return $ ((tracet $ toStrict $ pShow (lambdaToString' <$> l)) l) ++ ((concat ls) \\ l)
}

lambdas::(Show a, Enum a, Eq a) => a -> [Lambda a]
lambdas o = evalState (nextLambdas [] (Variable o)) (iterate succ o)
