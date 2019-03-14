module LambdaLearn where

import NewLogicM
import LambdaCompiler
import Control.Monad

------------------------------
--Lambda logic
------------------------------

--TODO: alpha equivalence

stdLamTer::(LogicM m) => m (Lambda Int)
stdLamTer = lamTer [1..]

lamTer::(LogicM m) => [a] -> m (Lambda a)
lamTer vars = lamTer' vars []
lamTer'::(LogicM m) => [a] ->  [a] -> m (Lambda a)
lamTer' vars bVars = (lamVar bVars) ||| (lamAbst vars bVars) ||| (lamAppl vars bVars)

lamTerArgs::(LogicM m) => Int -> [a] ->m (Lambda a, [Lambda a])
lamTerArgs n vars = lamTerArgs' n vars []
lamTerArgs'::(LogicM m) => Int -> [a] -> [a] -> m (Lambda a, [Lambda a])
lamTerArgs' 0 vars bVars = do {
  t <- lamTer' vars bVars;
  return (t, [])
}
lamTerArgs' n (v:vs) bVars =  do {
  (t,bnd) <- lamTerArgs' (pred n) vs (v:bVars);
  return (Abst v t, (Var v):bnd)
}

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
softBetaRed::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
softBetaRed t = ifte (recBetaRed t) return (return t)

recBetaRed::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
recBetaRed v@(Appl n m) = (betaRed v) |||
                        ((recBetaRed n) >>= (\n' -> return $ Appl n' m)) |||
                        ((recBetaRed m) >>= (\m' -> return $ Appl n m'))
recBetaRed (Abst x e)   = recBetaRed e >>= (\e' -> return $ Abst x e')
recBetaRed _   = fail'

recBetaRedSubt::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
recBetaRedSubt v@(Appl n m) = (betaRed v) ||| (recBetaRedSubt n) ||| (recBetaRedSubt m)
recBetaRedSubt (Abst x e)   = recBetaRedSubt e
recBetaRedSubt _   = fail'

run::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
run m = once $ run' m     --due to Church-Rosser
run'::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
run' t = ifte (recBetaRed t) run (return t)
-- take 1 $ toLst $(run $ lsi "(/1 1 1)(/1 1 1)")|||(return $ lsi "/1 1")

--computationally expensive nonhalting proof by induction over subterms
nonHaltByInd::(LogicM m, Eq a) => Lambda a -> m (Lambda a)
nonHaltByInd t = (once $ recursesNondetStateWith recBetaRedSubt t) >> return t

---------------------------------
--Lambda stuff
---------------------------------
--TODO: do this by set of equivalences
l_true::(LogicM m, Eq a) => [a] -> m (Lambda a)
l_true (arg1:arg2:vars) = once $ do {
  fkt <- lamTer vars;
  run (fkt <@> (Var arg1) <@> (Var arg2)) >>= sat (==(Var arg1));
  return fkt
}

l_false::(LogicM m, Eq a) => [a] -> m (Lambda a)
l_false (arg1:arg2:vars) = once $ do {
  fkt <- lamTer vars;
  run (fkt <@> (Var arg1) <@> (Var arg2)) >>= sat (==(Var arg2));
  return fkt
}

l_and::(LogicM m, Eq a) => [a] -> m (Lambda a)
l_and (vars) = once $ do {
  (fkt,[arg1,arg2]) <- lamTerArgs 2 vars;
  t <- l_true vars;
  f <- l_false vars;
  run (fkt <@> t <@> arg2) >>= sat (==arg2);
  run (fkt <@> f <@> arg2) >>= sat (==f);
  return fkt
}

l_or::(LogicM m, Eq a) => [a] -> m (Lambda a)
l_or (vars) = once $ do {
  (fkt,[arg1,arg2]) <- lamTerArgs 2 vars;
  t <- l_true vars;
  f <- l_false vars;
  run (fkt <@> f <@> arg2) >>= sat (==arg2);
  run (fkt <@> t <@> arg2) >>= sat (==t);
  return fkt
}

l_not::(LogicM m, Eq a) => [a] -> m (Lambda a)
l_not (vars) = once $ do {
  (fkt,[arg1]) <- lamTerArgs 1 vars;
  t <- l_true vars;                 --TODO: finally implement alpha equivalence! this equality breaks otherwise!
  f <- l_false vars;
  run (fkt <@> t) >>= sat (==f);
  run (fkt <@> f) >>= sat (==t);
  return fkt
}

l_impl::(LogicM m, Eq a) => [a] -> m (Lambda a)
l_impl (arg1:arg2:vars) = once $ do {
  v <- l_or vars;
  n <- l_not vars;
  run $ Abst arg1 $ Abst arg2 $ v <@> (n <@> (Var arg1)) <@> (Var arg2)
}

{-
--head, tail, isnull
l_lst::(LogicM m, Eq a) => [a] -> m (Lambda a, Lambda a, Lambda a)
l_lst (arg1:vars) = do {
  [hd, tl, isnull] <- carth 3 $ lamTer vars;
  run (t <@> (Var arg1) <@> (Var arg2)) >>= sat (==(Var arg2));
}
-}







---------------------------------
--debug
---------------------------------
debugLogLam::(Show a) => ResLst (Lambda a) -> IO ()
debugLogLam = debugLambdas.toLst





inductionTest = debugLambdas $ toLst $ do {
  t <- return $ (lsi "(/1 1 1)(/1 1 1)");
  join $ once $ recursesNondetStateWith recBetaRed t
}

inductionTest2 = debugLambdas $ toLst $ do {
  t <- return $ (lsi "/1(/2 (/3/4 4) 1 (2 2))(/2 (/3/4 4) 1 (2 2))");
  join $ once $ recursesNondetStateWith recBetaRed t
}

inductionTest3 = debugLambdas $ toLst $ do {
  t <- return $ (lsi "/1(/2 1(2 2))(/2 1(2 2))");
  join $ once $ recursesNondetStateWith recBetaRedSubt t --this one is needed for nonhalting of subterms
}

inductionTestUlt = debugLambdas $ toLst $ lamTer [1..] >>= nonHaltByInd



--TODO: only check nonterminism for part of formula
