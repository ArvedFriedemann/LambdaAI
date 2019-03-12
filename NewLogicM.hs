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
  split::m a -> m (Maybe (a, m a))
  ireturn::Maybe a -> m a

instance LogicM ResLst where
--(|||)::ResLst a -> ResLst a -> ResLst a
  (|||) (ELEM (Just x) xs) bs = ELEM (Just x) $ bs ||| xs
  (|||) (ELEM Nothing xs) bs = (ireturn Nothing) ||| (bs ||| xs)
  (|||) FAIL  bs = bs

  split (ELEM (Just a) ls)  = return $ Just (a, ls)
  split (ELEM Nothing ls)   = (ireturn Nothing) ||| (split ls)
  split FAIL                = return $ Nothing

--ireturn::Result a -> ResLst a
  ireturn x = ELEM x FAIL

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


lneg::(LogicM m) => m a -> m ()
lneg = softSplit (const fail') (return ())
