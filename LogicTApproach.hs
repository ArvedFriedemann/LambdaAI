module LogicTApproach where

import Control.Monad.Logic
import LambdaCompiler

(|||)::(MonadLogic m) => m a -> m a -> m a
(|||) = interleave

--TODO: force evaluate backwards!
sat::(MonadLogic m) => (a -> Bool) -> (a -> m a)
sat fkt = (\t -> (guard (fkt t)) >>- (\_ -> return t))

fairDisj::(MonadLogic m) => [m a] -> m a
fairDisj = foldr interleave mzero

forall::(MonadLogic m) => m a -> (a -> m ()) -> m ()
forall src pr = lnot $ src >>- (\x -> lnot (pr x))

lamTer::(MonadLogic m) => [a] -> m (Lambda a)
lamTer vars = lamTer' vars mzero
lamTer'::(MonadLogic m) => [a] ->  [a] -> m (Lambda a)
lamTer' vars bVars = (lamVar bVars) ||| (lamAbst vars bVars) ||| (lamAppl vars bVars)

lamVar::(MonadLogic m) => [a] -> m (Lambda a)
lamVar vars = fairDisj [return $ Var v | v <- vars]

lamAbst::(MonadLogic m) => [a] -> [a] -> m (Lambda a)
lamAbst (v:vs) bVars = lamTer' vs (v:bVars) >>- (\e -> return $ Abst v e)

lamAppl::(MonadLogic m) => [a] -> [a] -> m (Lambda a)
lamAppl vars bVars = (lamTer' vars bVars) >>-
                (\t1 -> lamTer' vars bVars >>-
                (\t2 -> return $ Appl t1 t2))


--putStrLn $ unlines $ map lambdaToString' $ take 5 $ (lamTer [1..]) >>= sat (==Abst 1 (Abst 2 (Appl (Var 1) (Var 2))) )
