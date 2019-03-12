module NewLogicM where

import Data.Maybe
import Control.Monad.Plus
import Control.Monad
import Control.Monad.Trans.Maybe


type Result a = Maybe a
data ResLst a = ELEM (Result a) (ResLst a) | FAIL

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
  (>>=) (ELEM (Just f) fs) fkt = (fkt f) ||| (fs >>= fkt)
  (>>=) (ELEM Nothing fs) fkt = (ireturn Nothing) ||| (fs >>= fkt)
  (>>=) FAIL fkt = FAIL

  fail _ = FAIL

class (Monad m) => LogicM m where
  (|||)::m a -> m a -> m a
  split::(a -> m a -> b) -> (m a -> b) -> b -> m a -> m b
  ireturn::Maybe a -> m a

instance LogicM ResLst where
--(|||)::ResLst a -> ResLst a -> ResLst a
  (|||) (ELEM (Just x) xs) bs = ELEM (Just x) $ bs ||| xs
  (|||) (ELEM Nothing xs) bs = bs ||| xs
  (|||) FAIL  bs = bs

--split::(a -> ResLst a -> b) -> (ResLst a -> b) -> b -> ResLst a -> ResLst b
  split fkt _ _    (ELEM (Just a) ls)  = fkt a ls
  split _ nCase _  (ELEM Nothing ls)   = nCase ls
  split _ _ aCase  FAIL              = aCase

--ireturn::Result a -> ResLst a
  ireturn x = ELEM x FAIL

fail'::(LogicM m) => m a
fail' = fail ""

softSplit::(LogicM m) => (a -> m b) -> m b -> m a -> m b
softSplit fkt aCase = split (\v ts -> (fkt v)) (\ts -> (ireturn Nothing)|||(softSplit fkt aCase ts)) aCase

once::(LogicM m) => m a -> m a
once = softSplit return fail'

ifte::(LogicM m) => m a -> (a -> m b) -> m b -> m b
ifte m t f = softSplit t f m

lneg::(LogicM m) => m a -> m ()
lneg = softSplit (const fail') (return ())
