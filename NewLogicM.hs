module NewLogicM where

import Data.Maybe
import Control.Monad.Plus
import Control.Monad
import Control.Monad.Trans.Maybe


type Result a = Maybe a
data ResLst a = ELEM (Result a) (ResLst a) | FAIL deriving (Eq, Show)

toLst::ResLst a -> [a]
toLst (ELEM (Just a) ls) = a:(toLst ls)
toLst (ELEM Nothing ls) = (toLst ls)
toLst FAIL = []
fromLst::[a] -> ResLst a
fromLst lst = foldr (\v-> ELEM (Just v)) FAIL lst


instance Functor ResLst where
--fmap::(Functor f) => (a -> b) -> f a -> f b
  fmap f (ELEM (Just x) xs) = ELEM (Just $ f x) (fmap f xs)
  fmap f (ELEM Nothing xs) = ELEM Nothing (fmap f xs)
  fmap f FAIL = FAIL
instance Applicative ResLst where
--(<*>) :: Applicative f => f (a -> b) -> f a -> f b
  (<*>) (ELEM (Just f) fs) b@(ELEM (Just x) xs) = ELEM (Just $ f x) $ (fmap f xs) ||| (fs <*> b)
  (<*>) (ELEM Nothing fs) b = fs <*> b
  (<*>) FAIL _ = FAIL
  pure x = ELEM (Just x) FAIL
instance Monad ResLst where
--(>>=) :: Monad m => m a -> (a -> m b) -> m b
  (>>=) (ELEM (Just f) fs) fkt = unknown ||| (fkt f) ||| (fs >>= fkt)
  (>>=) (ELEM Nothing fs) fkt = unknown ||| (fs >>= fkt)
  (>>=) FAIL fkt = FAIL

  fail _ = FAIL

class (Monad m) => LogicM m where
  (|||)::m a -> m a -> m a
  split::m a -> m (Maybe (a, m a))
  unknown:: m a

instance LogicM ResLst where
--(|||)::ResLst a -> ResLst a -> ResLst a
  (|||) (ELEM (Just x) xs) bs = ELEM (Just x) $ bs ||| xs
  (|||) (ELEM Nothing xs) bs = ELEM Nothing (bs ||| xs)
  (|||) FAIL  bs = bs

  split (ELEM (Just a) ls)  = return $ Just (a, ls)
  split (ELEM Nothing ls)   = (unknown) ||| (split ls)
  split FAIL                = return $ Nothing

--ireturn::Result a -> ResLst a
  unknown = ELEM Nothing FAIL

(\/)::(LogicM m) => [a] -> m a
(\/) = fairDisj.(return <$>)

fairDisj::(LogicM m) => [m a] -> m a
fairDisj = foldr (|||) fail'

fail'::(LogicM m) => m a
fail' = fail ""

ifte::(LogicM m) => m a -> (a -> m b) -> m b -> m b
ifte m t f = do{
  res <- split m;
  case res of
    Just (x, m) -> (t x) ||| (m >>= t)
    Nothing -> f
}

--Warning: Performs a "once"
softSplit::(LogicM m) => (a -> m b) -> m b -> m a -> m b
softSplit fkt nCase m = do{
  res <- split m;
  case res of
    Just (x, _) -> fkt x
    Nothing -> nCase
}

once::(LogicM m) => m a -> m a
once = softSplit return fail'

lnot::(LogicM m) => m a -> m ()
lnot = softSplit (const fail') (return ())

--returns the monad
forall::(LogicM m) => m a -> (a -> m b) -> m (m a)
forall m fkt = lnot (m >>= (lnot.fkt)) >> (return m)

--checks whether the monad is non empty. returns the monad
atLeastOne::(LogicM m) => m a -> m (m a)
atLeastOne m = ifte (once $ m) (const (return m)) fail'

sat::(LogicM m) => (a -> Bool) -> a -> m a
sat fkt a
  | fkt a = return a
  | otherwise = fail'

sat2::(LogicM m) => (a -> b -> Bool) -> a -> b -> m ()
sat2 fkt a b
  | fkt a b = return ()
  | otherwise = fail'


is::(LogicM m) => Bool -> m ()
is True = return ()
is False = fail'

prolly::(LogicM m) => a -> (a -> m b) -> m ()
prolly v c = (c v >> return ()) ||| (return ())

--returns the first monad
equiv::(LogicM m, Eq a) => m a -> m a -> m (m a)
equiv m1 m2 = forall m1 (\t1 -> m2 >>= sat (== t1))

equi::(LogicM m, Eq a) => a -> a -> m a
equi a b = sat (==b) a

carth::(LogicM m) => Int -> m a -> m [a]
carth 0 _ = return []
carth n m = do {r <- m; res <- carth (pred n) m; return $ r:res}

--Notice: Not efficient for use in bidirectional search. Turns out
--to be equivalent to usual search with start point generator
--gets the input value that goes to a specific output value
revPredEq::(LogicM m) => (a -> a -> m c) -> m b -> (b -> m a) -> a -> m b
revPredEq eq m fkt s = do {
  v <- m;
  v' <- fkt v;
  eq v' s;
  return v
}

--------------------------------------------
--automata operations
--------------------------------------------

reaches::(LogicM m) => (a -> m a) -> a -> m a
reaches fkt m = do {
  r <- fkt m;
  (return r) ||| (reaches fkt r)
}

--needs equality predicate
--computes whether the target is hit from the source
hitsWith::(LogicM m) => (a -> a -> m b) -> (a -> m a) ->  a -> a -> m ()
hitsWith eq fkt a b = once $ reaches fkt a >>= eq b >> return ()


--needs equality predicate, returns the state that is being recursed
recursesStateWith::(LogicM m) => (a -> a -> m b) -> (a -> m a) ->  a -> m a
recursesStateWith eq fkt s = ((return s) ||| reaches fkt s) >>= (\t -> hitsWith eq fkt t t >> return t)

--returns the recursed set
recursesNondetStateWith::(LogicM m, Eq a) => (a -> m a) -> a -> m (m a)
recursesNondetStateWith fkt s = recursesStateWith equiv (\m -> atLeastOne (successors m)) (return s)
  where successors = \m -> join $ fkt <$> m

--recursesNondetStateWith fkt s = recursesStateWith equiv (\m -> return $ join $ fkt <$> m) (return s) --TODO: something doesn't work in power set
