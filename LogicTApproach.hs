module LogicTApproach where

import Control.Monad.Logic
import LambdaCompiler
import Debug.Trace

(|||)::(MonadLogic m) => m a -> m a -> m a
(|||) = interleave

----------------------
--lambda misc
----------------------
formSize::Lambda a -> Int
formSize (Var _) = 1
formSize (Abst x e) = 1+(formSize e)
formSize (Appl n m) = 1+(formSize n)+(formSize m)

upperFormSize::(MonadLogic m) => Int -> Lambda a -> m (Lambda a)
upperFormSize s = sat ((<= s).formSize)

----------------------
--logic stuff
----------------------

--TODO: force evaluate backwards!
sat::(MonadLogic m) => (a -> Bool) -> (a -> m a)
sat fkt = satM $ (\t -> guard (fkt t))

sat'::(MonadLogic m) => (a -> Bool) -> (a -> m ())
sat' fkt = (\t -> guard (fkt t))

satM::(MonadLogic m) => (a -> m ()) -> (a -> m a)
satM m = (\t -> m t >>- (\_ -> return t))

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

nBetaRed::(MonadLogic m, Eq a) => Lambda a -> m (Lambda a)
nBetaRed t = (return t) ||| (rBetaRed t)
rBetaRed::(MonadLogic m, Eq a) => Lambda a -> m (Lambda a)
rBetaRed v@(Appl n m) = (betaRed v) |||
                        ((rBetaRed n) >>- (\n' -> return $ Appl n' m)) |||
                        ((rBetaRed m) >>- (\m' -> return $ Appl n m'))
rBetaRed (Abst x e)   = rBetaRed e >>- (\e' -> return $ Abst x e')
rBetaRed _   = mzero

betaRed::(MonadLogic m, Eq a) => Lambda a -> m (Lambda a)
betaRed (Appl (Abst x e) y) = return $ change e x y
betaRed _ = mzero

change::(Eq a) => Lambda a -> a -> Lambda a -> Lambda a
change v@(Var x) a b
  | x==a = b
  | otherwise = v
change v@(Abst x e) a b
  | x==a = v --variable now has different meaning
  | otherwise = Abst x (change e a b)
change (Appl n m) a b = Appl (change n a b) (change m a b)

reaches::(MonadLogic m, Eq a) => Lambda a -> m (Lambda a)
reaches = fairIterateM rBetaRed

run::(MonadLogic m, Eq a) => Lambda a -> m (Lambda a)
run t = ifte (rBetaRed t) run (return t)

runAtMost::(MonadLogic m, Eq a) => Int -> Lambda a -> m (Lambda a)
runAtMost i t = fairIterateNM i nBetaRed t

fairIterateNM::(MonadLogic m) => Int -> (a -> m a) -> a -> m a
fairIterateNM 0 _ a = return a
fairIterateNM n f a = (f a) >>- (fairIterateNM (pred n) f)

fairIterateM::(MonadLogic m) => (a -> m a) -> a -> m a
fairIterateM m t = (return t) ||| ((m t) >>- (fairIterateM m))
-----------------------------------------
--learning
-----------------------------------------

-- /vars. E
lov = lineOfVars
lineOfVars::[a] -> Lambda a -> Lambda a
lineOfVars vars e = foldr Abst e vars

l_idfr::[a] -> Int -> Lambda a
l_idfr vars k = lineOfVars vars $ Var (vars !! k)

applLst::[Lambda a] -> Lambda a
applLst lst = foldl1 Appl lst

--TODO: intput and output need to be represented as lists. Otherwise constants will be applied to each other
--variables, number of Constants, function (assumed to have same input and output length for now)
learn::(MonadLogic m, Eq a, Show a) => [a] -> Int -> m ([Int],[Int]) -> m (Lambda a)
learn vars cNum table = (fairDisj $ return <$> [1..]) >>= (\b ->
                        (lamTer' restV cnst) >>- upperFormSize b >>-
                        satM (\t -> traceShow (lambdaToString' t) $ forall table
                                (\(ai,bi) -> run ((\r -> trace (lambdaToString' r) r) $ applLst $ (fstp t):((l_idfr cnst) <$> ai) )  >>-
                                  sat' ((==) (applLst $ (l_idfr cnst) <$> bi)) ) ) )
  where (cnst,restV) = (take cNum vars, drop cNum vars)
        fstp = \t -> applLst $ (lineOfVars cnst t):((l_idfr cnst) <$> [0..(cNum-1)]) --give a function the implementation of the identifiers

learnBool::(MonadLogic m, Eq a, Show a) => [a] ->  m ([Bool],[Bool]) -> m (Lambda a)
learnBool vars table = learn vars 2 ((\(a,b) -> (boolToInt <$> a, boolToInt <$> b)) <$> table)

boolToInt::Bool -> Int
boolToInt False = 0
boolToInt True = 1

boolLearnTest = lambdaToString' $ head $ learnBool [1..]
                        [([False,False],[False]),
                         ([False,True ],[True]),
                         ([True ,False],[True]),
                         ([True ,True ],[False])]
