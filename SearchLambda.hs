module SearchLambda where

import LambdaCompiler
import Data.List
import Control.Monad.Trans.State.Lazy
import Debug.Trace
import Data.Text.Lazy (toStrict)
import Text.Pretty.Simple
import TextShow.Debug.Trace
import Control.Monad.Logic

type VarMon a b = State [a] b

next::VarMon a a
next = state (\x -> (head x, tail x))

--vars, current bond Vars, "empty" symbol, current term
nextLambda::(Eq a) => [a] -> a -> Lambda a -> [Lambda a]
nextLambda stack e (Var _) =  (Var <$> stack)++[Abst e x | x <- (Var <$> (e:stack))]
nextLambda stack e (Abst x y) = [Abst x z | z <- nextLambda (x:stack) e y] ++
                                        (nextLambda stack e (Appl (Var e) (Var e)))
nextLambda stack e (Appl a b) = [Appl x y | x <- nextLambda stack e a, y <- nextLambda stack e b]

--v needs to be a brand new Var
prevLambda::(Eq a) => a -> Lambda a -> [Lambda a]
prevLambda v l = [Appl (Abst v (lightReverseBetaReduction q v l)) q |
                    q <- (map head) $ filter (not.null.(drop 1)) (group $ subformulas l)]++
                  [Appl (Abst v l) (Var v)] --the constant function, where the second option can be any term

--previous
nextLambdas::(Show a, Enum a, Eq a) => [Lambda a] -> a ->  Lambda a -> [[Lambda a]]
nextLambdas = nextLambdasN (-1)
nextLambdasN::(Show a, Enum a, Eq a) => Int -> [Lambda a] -> a ->  Lambda a -> [[Lambda a]]
nextLambdasN 0 _ _ _ = []
nextLambdasN i prev e cl = nextList : (concat $ transpose $ (nextLambdasN (pred i) (nextList++prev) e) <$> (nextList))
  where nextList = nub (((renameDubs succ) <$> (nextLambda [] e cl)) \\ (cl:prev))

lambdas::(Show a, Enum a, Eq a) => a -> [[Lambda a]]
lambdas o =  (nextLambdas [] o (Var o))

l_id::DeBrujLambda
l_id = lsd "/1 1"
l_true::DeBrujLambda
l_true = lsd "/2/1 2"
l_false::DeBrujLambda
l_false = lsd "/2/1 1"
l_tuple::DeBrujLambda
l_tuple = lsd "/3/2/1 1 3 2"
l_fst::DeBrujLambda
l_fst = lsd "/3 3 (/2/1 2)"
l_snd::DeBrujLambda
l_snd = lsd "/3 3 (/2/1 1)"
l_zero::DeBrujLambda
l_zero = lsd "/1 /2 2"
l_succ::DeBrujLambda
l_succ = lsd "/1/2/3 2(1 2 3)"
l_iszero::DeBrujLambda
l_iszero = lsd "/1 1 (/3/4 /5/6 6) (/1 1) (/2/1 2)"

l_Var::DeBrujLambda
l_Var = lsd "/value/c c (/1/2/3 1) value"
l_Abst::DeBrujLambda
l_Abst = lsd "/term/c c (/1/2/3 2) term"
l_Appl::DeBrujLambda
l_Appl = lsd "/term1/term2/c c (/1/2/3 3) term1 term2"


--TODO: can I learn a lambda function by using them as case distinctions and putting the constructors?
--just eath them in and leanr the substitutions "by heart" but then occasionally equal two indices...hehe
--so a function applied to something becomes something else. Some functions eath certain things while others don't.
--the case distinction is what you apply it to. If it is eathen then it couldn't have been the function...something like this

curchnum::Integer -> DeBrujLambda
curchnum i = runDeBruj $ (iterate (l_succ<>) l_zero) !! (fromInteger i)

encodeLam::DeBrujLambda -> DeBrujLambda
encodeLam = runDeBruj.encodeLam'
encodeLam'::DeBrujLambda -> DeBrujLambda
encodeLam' (BVar x) = l_Var <> (curchnum x)
encodeLam' (BAbst x) = l_Abst <> (encodeLam x)
encodeLam' (BAppl n m) = l_Appl <> (encodeLam n) <> (encodeLam m)

stepFunctions::Int -> [Lambda Integer]
stepFunctions s = [evl | evl <- concat $ lambdas 0,
            and [(runDeBrujN (10*s) ((lamToDeBruj evl) <> l)) == (runDeBrujN s l) | l <- lamToDeBruj <$> (concat $ nextLambdasN s [] 0 (Var 0))]]
{-
lambdaToLambda'::a -> a -> a -> Lambda Int -> Lambda Int
lambdaToLambda' var abst appl (Var x) =

searchCompiler::Int -> [Lambda a]
searchCompiler = []
-}
