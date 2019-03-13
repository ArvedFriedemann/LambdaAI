module LambdaLearn where

import NewLogicM
import LambdaCompiler
import Control.Monad

--TODO: alpha equivalence

lamTer::(LogicM m) => [a] -> m (Lambda a)
lamTer vars = lamTer' vars []
lamTer'::(LogicM m) => [a] ->  [a] -> m (Lambda a)
lamTer' vars bVars = (lamVar bVars) ||| (lamAbst vars bVars) ||| (lamAppl vars bVars)

lamVar::(LogicM m) => [a] -> m (Lambda a)
lamVar vars = fairDisj [return $ Var v | v <- vars]

lamAbst::(LogicM m) => [a] -> [a] -> m (Lambda a)
lamAbst (v:vs) bVars = lamTer' vs (v:bVars) >>= (\e -> return $ Abst v e)

lamAppl::(LogicM m) => [a] -> [a] -> m (Lambda a)
lamAppl vars bVars = do {
  t1 <- lamTer' vars bVars;
  t2 <- lamTer' vars bVars;
  return $ Appl t1 t2
}



betaRed::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
betaRed (Appl (Abst x e) y) = return $ change e x y
betaRed _ = fail'

change::(Eq a) => Lambda a -> a -> Lambda a -> Lambda a
change v@(Var x) a b
  | x==a = b
  | otherwise = v
change v@(Abst x e) a b
  | x==a = v --variable now has different meaning
  | otherwise = Abst x (change e a b)
change (Appl n m) a b = Appl (change n a b) (change m a b)

nBetaRed::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
nBetaRed t = (return t) ||| (recBetaRed t)
recBetaRed::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
recBetaRed v@(Appl n m) = (betaRed v) |||
                        ((recBetaRed n) >>= (\n' -> return $ Appl n' m)) |||
                        ((recBetaRed m) >>= (\m' -> return $ Appl n m'))
recBetaRed (Abst x e)   = recBetaRed e >>= (\e' -> return $ Abst x e')
recBetaRed _   = fail'

run::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
run m = once $ run' m     --due to Church-Rosser
run'::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
run' t = ifte (recBetaRed t) run (return t)
-- take 1 $ toLst $(run $ lsi "(/1 1 1)(/1 1 1)")|||(return $ lsi "/1 1")

inductionTest = debugLambdas $ toLst $ do {
  t <- return $ (lsi "(/1 1 1)(/1 1 1)");
  join $ once $ recursesNondetStateWith recBetaRed t
}

inductionTest2 = debugLambdas $ toLst $ do {
  t <- return $ (lsi "/1(/2 1(2 2))(/2 1(2 2))");
  join $ once $ recursesNondetStateWith recBetaRed t
}



--TODO: only check nonterminism for part of formula
