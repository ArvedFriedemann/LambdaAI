module SearchLambda where

#include LambdaCompiler

lambdaExpressions::[a] -> [Lambda a]
lambdaExpressions vars =
    where initial = (Variable <*> vars)
          curr = [foldr Abstraction x vars | x <- initial++(nextLambda initial) ]


--TODO: how to give handles for making this faster? Some set operations would be good!
--variables, varstack, current lambda, next lambdas
nextLambda::[a] -> [a] -> Lambda a -> [[Lambda a]]
nextLambda vars stack (Variable _) = [[Abstraction x (Variable y) | y <- x:stack] | x <- vars]
nextLambda vars stack (Abstraction x y) = [Abstraction x z | z <- nextLambda y] ++ [Application (Variable a) (Variable b) | x <- vars, y <- vars]
nextLambda vars stack (Application a b) = [Application x y | x <- nextLambda a, y <- nextLambda b]
