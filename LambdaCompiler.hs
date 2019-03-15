module LambdaCompiler where

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Data.List
import Data.Either
import Data.Maybe
import Debug.Trace
import Text.Parsec.Token
import Debug.Trace
import Test.QuickCheck
import Test.QuickCheck.Gen
import GHC.Generics
import Text.Pretty.Simple

data LamFkt a b = Fkt (a -> b) | T b
data Lambda a = Var a | Abst a (Lambda a) | Appl (Lambda a) (Lambda a) deriving (Eq, Show)
instance (Arbitrary a) => Arbitrary (Lambda a) where
   arbitrary = sized arbitrarySizedLambda
arbitrarySizedLambda:: Arbitrary a => Int -> Gen (Lambda a)
arbitrarySizedLambda 0 = do{v <- arbitrary; return $ Var v}
arbitrarySizedLambda s = do {
  c <- elements [0,1,2];
  case c of
    0 -> Var <$> arbitrary;
    1 -> (Abst <$> arbitrary) <*> (arbitrarySizedLambda (pred s))
    2 -> do{
      v1 <- arbitrarySizedLambda (pred s);
      v2 <- arbitrarySizedLambda (pred s);
      return $ Appl v1 v2}
}
type NamedDeBrujLambda  = Lambda Integer
data DeBrujLambda = BVar Integer | BAbst (DeBrujLambda) | BAppl (DeBrujLambda) (DeBrujLambda) deriving (Eq, Show)

subformulas::Lambda a -> [Lambda a]
subformulas q@(Var x) = [q]
subformulas q@(Abst x e) = q:(subformulas e)
subformulas q@(Appl n m) = q:((subformulas n) ++ (subformulas m))

varsDB::DeBrujLambda -> [Integer]
varsDB (BVar x) = [x]
varsDB (BAbst m) = varsDB m
varsDB (BAppl n m) = (varsDB n) ++ (varsDB m)

remNames::NamedDeBrujLambda -> DeBrujLambda
remNames (Var x) = BVar x
remNames (Abst _ x) = BAbst (remNames x)
remNames (Appl m n) = BAppl (remNames m) (remNames n)

lamToDeBruj::(Eq a) => Lambda a -> DeBrujLambda
lamToDeBruj = remNames.lamToNamDeBruj

alphaEquiv::(Eq a) => Lambda a -> Lambda a -> Bool
alphaEquiv l1 l2 = (l1 == l2) || ((lamToDeBruj l1) == (lamToDeBruj l2))

deBrujToString::DeBrujLambda -> String
deBrujToString = lambdaToString'.backToLambda

deBrujToBrString::DeBrujLambda -> String
deBrujToBrString = lambdaToBracketString'.backToLambda

--TODO: doesn't work (Var to Abst binding fail)
backToLambda::DeBrujLambda -> Lambda Integer
backToLambda db = renameDubs succ $ mapNames (+(-maxdb)) $ backToLambda' $ markByDepth [maxdb..] db
  where maxdb = (+1) $ maximum $ varsDB db

backToLambda'::NamedDeBrujLambda -> Lambda Integer
backToLambda' (Var x) = Var x
backToLambda' (Abst n x) = Abst n (backToLambda' $ renameCurrDepth 1 n x) --only works if n doesn't cause name clashes!
backToLambda' (Appl m n) = Appl (backToLambda' m) (backToLambda' n)

renameCurrDepth::Integer -> Integer -> NamedDeBrujLambda -> NamedDeBrujLambda
renameCurrDepth i a (Var x)
                            | i==x = Var a
                            | otherwise = Var x
renameCurrDepth i a (Abst n m) = Abst n (renameCurrDepth (succ i) a m)
renameCurrDepth i a (Appl n m) = Appl (renameCurrDepth i a n) (renameCurrDepth i a m)

markByDepth::[Integer] -> DeBrujLambda -> NamedDeBrujLambda
markByDepth a (BVar x) = Var x
markByDepth (a:as) (BAbst x) = Abst a (markByDepth as x)
markByDepth a (BAppl m n) = Appl (markByDepth a m) (markByDepth a n)

anyName::DeBrujLambda -> NamedDeBrujLambda
anyName = anyName' 0
anyName'::Integer -> DeBrujLambda -> NamedDeBrujLambda
anyName' a (BVar x) = Var x
anyName' a (BAbst x) = Abst a (anyName' a x)
anyName' a (BAppl m n) = Appl (anyName' a m) (anyName' a n)

infixl 9 <>
(<>)::DeBrujLambda -> DeBrujLambda -> DeBrujLambda
(<>) a b = BAppl a b
infixl 9 <@>
(<@>)::Lambda a -> Lambda a -> Lambda a
(<@>) a b = Appl a b

varCont::Lambda a -> a
varCont (Var a) = a

mapNames::(a->b) -> Lambda a-> Lambda b
mapNames f (Var x) = Var (f x)
mapNames f (Abst x lx) = Abst (f x) (mapNames f lx)
mapNames f (Appl n m) = Appl (mapNames f n) ( mapNames f m)

lambdaToString'::(Show a) => Lambda a -> String
lambdaToString' = lambdaToString.(mapNames show)
lambdaToString::Lambda String -> String
lambdaToString (Var x)       = x
lambdaToString (Abst x lx@(Abst _ _)) = "/"++x++(lambdaToString lx)
lambdaToString (Abst x lx) = "/"++x++" "++(lambdaToString lx)
lambdaToString (Appl n@(Abst _ _) m@(Abst _ _)) = "("++(lambdaToString n)++")"++"("++(lambdaToString m)++")"
--lambdaToString (Appl n m@(Abst _ _)) = (lambdaToString n)++" ("++(lambdaToString m)++")"
lambdaToString (Appl n@(Abst _ _) m@(Appl _ _)) =  "("++(lambdaToString n)++") ("++(lambdaToString m)++")"
lambdaToString (Appl n@(Appl _ _) m@(Appl _ _)) =  "("++(lambdaToString n)++") "++(lambdaToString m)
lambdaToString (Appl n@(Abst _ _) m) = "("++(lambdaToString n)++")"++(lambdaToString m)
lambdaToString (Appl n m@(Appl _ _)) = (lambdaToString n)++" ("++(lambdaToString m)++")"
lambdaToString (Appl n m@(Abst _ _)) = (lambdaToString n)++" ("++(lambdaToString m)++")"
lambdaToString (Appl n m) = (lambdaToString n)++" "++(lambdaToString m)

testParser::Lambda Int -> Bool
testParser x = (lambdaFromString $ lambdaToString (modf x)) == (lambdaFromString $ lambdaToBracketString (modf x))
                          where modf = (mapNames show)

lambdaToTreeString l = lambdaToTreeString' l ""
lambdaToTreeString'::Lambda String -> String -> String
lambdaToTreeString' (Var x) s       = s++x++"\n"
lambdaToTreeString' (Abst x lx) s = s++"/"++x++"\n"++(lambdaToTreeString' lx (s++"\t"))++"\n"
lambdaToTreeString' (Appl n m)  s = s++"."++"\n"++(lambdaToTreeString' n (s))++(lambdaToTreeString' m (s))++"\n"

lambdaToBracketString'::(Show a) => Lambda a -> String
lambdaToBracketString' = lambdaToBracketString.(mapNames show)
lambdaToBracketString::Lambda String -> String
lambdaToBracketString (Var x)       = x
lambdaToBracketString (Abst x lx) = "(/"++x++" "++(lambdaToBracketString lx)++")"
lambdaToBracketString (Appl n m)  = "("++(lambdaToBracketString n)++" "++(lambdaToBracketString m)++")"

--(Abst 0 (Appl (Abst 1 (Var 1) ) (Var 0)))

numberVars::(Eq a) => Lambda a -> Lambda Integer
numberVars t = mapNames (toInteger.fromJust.((flip elemIndex) $ vars t)) t

ls = lambdaFromString
lsd::String -> DeBrujLambda
lsd = lamToDeBruj.lambdaFromString
lsa::(Read a) => String -> Lambda a
lsa = (mapNames read).lambdaFromString
lsi::String -> Lambda Int
lsi = lsa
--lsI::String -> Lambda Integer
--lsI = numberVars.lsa
lambdaFromString::String -> Lambda String
lambdaFromString s = case parse parseLambda "" s of
                        Right a -> a
                        Left err -> error $ show err

parseLambda::Parsec String a (Lambda String)
parseLambda = (foldl1 Appl) <$> (many1 parseSingleLambda)

parseSingleLambda::Parsec String a (Lambda String)
parseSingleLambda = skipSpace >> ((try $ parseAbst) <|> (try $ parseVar) <|> (paren parseLambda))

parseVar::Parsec String a (Lambda String)
parseVar = skipSpace >> (Var <$> many1 (noneOf " /()"))
parseAbst::Parsec String a (Lambda String)
parseAbst = do{
                skipSpace >> (string"/");
                v <- parseVar;
                (Abst $ varCont v) <$> parseLambda}

exchangeFirstLeftAssoc::Lambda a -> Lambda a -> Lambda a
exchangeFirstLeftAssoc t (Appl start@(Appl _ _) end) = Appl (exchangeFirstLeftAssoc t start) end
exchangeFirstLeftAssoc t x = Appl t x

reverseAppAssoc::Lambda a -> Lambda a
reverseAppAssoc (Appl x (Appl y z)) = reverseAppAssoc $ Appl (Appl x y) z
reverseAppAssoc x = x

skipSpace::Parsec String a String
skipSpace = many $ oneOf " \t\n"
paren::Parsec String a b -> Parsec String a b
paren p = do{skipSpace; char '('; skipSpace; r <- p; skipSpace; char ')'; skipSpace; return r}


vars::(Eq a) => Lambda a -> [a]
vars (Var x)       = [x]
vars (Abst x lx) = x:(vars lx)
vars (Appl x y)  = (vars x)++(vars y)

bounds::(Eq a ) => Lambda a -> [a]
bounds (Var _)       = []
bounds (Abst x lx) = x:(bounds lx)
bounds (Appl x y)  = (bounds x)++(bounds y)

unbounds::(Eq a) => Lambda a -> [a]
unbounds l = unbounds' l []

unbounds'::(Eq a) => Lambda a -> [a] -> [a]
unbounds' (Var x)       acc = [x]\\acc
unbounds' (Abst x lx) acc = unbounds' lx (x:acc)
unbounds' (Appl x y)  acc = union (unbounds' x acc) (unbounds' y acc)

intVars::(Eq a) => Lambda a -> Lambda Integer
intVars = fst.intVars'
intVars'::(Eq a) => Lambda a -> (Lambda Integer, [(a,Integer)])
intVars' t = (mapNames (fromJust.(\x -> lookup x mapping)) t, mapping)
  where mapping = zip (vars t) [1..]

lamToNamDeBruj::(Eq a) => Lambda a -> NamedDeBrujLambda
lamToNamDeBruj l = lamToNamDeBruj' (intVars l) (const 0) 0

--expression, naming function, depth
lamToNamDeBruj'::Lambda Integer ->(Integer -> Integer) -> Integer -> NamedDeBrujLambda
lamToNamDeBruj' (Var x)     f d = Var $ d - (f x)
lamToNamDeBruj' (Abst x lx) f d = Abst x $ lamToNamDeBruj' lx (\y -> if (y==x) then d else f y) (succ d)
lamToNamDeBruj' (Appl n m)  f d = Appl (lamToNamDeBruj' n f d) (lamToNamDeBruj' m f d)

validifyUnbound::(Eq a)=> Lambda a -> Lambda a
validifyUnbound l = foldr Abst l (unbounds l)

--TODO: broken
renameDubs::(Eq a, Show a) => (a -> a) -> Lambda a -> Lambda a
renameDubs f = renameDubs' f []
renameDubs'::(Eq a, Show a) => (a -> a) -> [a] -> Lambda a -> Lambda a
renameDubs' f stack (Var x)        = Var x
renameDubs' f stack (Abst x lx)
                                  | x `elem` stack = Abst x' $ renameDubs' f (x':stack) (alphaReduction x x' lx)
                                  | otherwise = Abst x $ renameDubs' f (x:stack) lx
                                  where x' = (head $ dropWhile (flip elem $ (x:stack)) $ iterate f x)
renameDubs' f stack (Appl n m)   = Appl (renameDubs' f stack n) (renameDubs' f stack m)

--search for a certain Abst binding the Var v
searchAbst::(Eq a) => a -> Lambda a -> (Lambda a -> Lambda a) -> Lambda a
searchAbst v a@(Var x) f = a
searchAbst v a@(Abst x lx) f
                            |v==x = f a
                            |otherwise = Abst x (searchAbst v lx f)
searchAbst v (Appl n m) f = Appl (searchAbst v n f) (searchAbst v m f)

--important: stops at Abst (don't continue renaming)
alphaReduction::(Eq a, Show a) => a -> a -> Lambda a -> Lambda a
alphaReduction a b (Var c)
                |a==c = Var b
                |otherwise = Var c
alphaReduction a b q@(Abst c lx)
                |a==c = q --now the Var has a different meaning
                |otherwise = Abst c (alphaReduction a b lx)
alphaReduction a b (Appl n m) = Appl (alphaReduction a b n) (alphaReduction a b m)

exchangeVar::(Eq a) => a -> Lambda a -> Lambda a -> Lambda a
exchangeVar a t (Var c)
                |a==c = t
                |otherwise = Var c
exchangeVar a t q@(Abst c lx)
                |a==c = q --now the Var has a different meaning
                |otherwise = Abst c (exchangeVar a t lx)
exchangeVar a t (Appl n m) = Appl (exchangeVar a t n) (exchangeVar a t m)

--TODO: should be made deprecated
--beta reduction with renaming function. Returns additionally whether the term has halted (any computation has been done)
betaReductionLMOM::(Eq a, Show a) => (a->a) -> Lambda a -> (Bool, Lambda a)
betaReductionLMOM f (Appl (Abst x e) y)
                                          | not comp = (True, renameDubs f $ exchangeVar x y e)
                                          | otherwise = (True, Appl (Abst x res) y)
                              where (comp, res) = betaReductionLMOM f e
betaReductionLMOM f a@(Appl m n)
                                          | compM = (True, Appl m' n)
                                          | compN = (True, Appl m n')
                                          | otherwise = (False, a)
                              where (compM, m') = betaReductionLMOM f m
                                    (compN, n') = betaReductionLMOM f n
betaReductionLMOM f (Abst x e) = (comp, Abst x res)
                              where (comp, res) = (betaReductionLMOM f e)
betaReductionLMOM _ x = (False, x)

--assumes DeBrujin normal form (no renaming required). Names still kept for convenience
betaReductionLMOMDeBruj:: NamedDeBrujLambda -> (Bool, NamedDeBrujLambda)
betaReductionLMOMDeBruj (Appl (Abst x e) y)
                                          | not comp = (True, betaReductionDeBruj' 1 y e) --1 because we already jumped into one Abst
                                          | otherwise = (True, Appl (Abst x res) y)
                              where (comp, res) = betaReductionLMOMDeBruj e
betaReductionLMOMDeBruj a@(Appl m n)
                                          | compM = (True, Appl m' n)
                                          | compN = (True, Appl m n')
                                          | otherwise = (False, a)
                              where (compM, m') = betaReductionLMOMDeBruj m
                                    (compN, n') = betaReductionLMOMDeBruj n
betaReductionLMOMDeBruj (Abst x e) = (comp, Abst x res)
                              where (comp, res) = (betaReductionLMOMDeBruj e)
betaReductionLMOMDeBruj x = (False, x)


betaReductionDeBruj'::Integer -> NamedDeBrujLambda -> NamedDeBrujLambda -> NamedDeBrujLambda
betaReductionDeBruj' i t a@(Var x)
                            | i == x = t
                            | otherwise = a
betaReductionDeBruj' i t (Abst n m) = Abst n (betaReductionDeBruj' (succ i) t m)
betaReductionDeBruj' i t (Appl n m) = Appl (betaReductionDeBruj' i t n) (betaReductionDeBruj' i t m)

--term, Var, bigger term. exchanges the _exact_ term in the bigger term with the Var
lightReverseBetaReduction::(Eq a) => Lambda a -> a -> Lambda a -> Lambda a
lightReverseBetaReduction t v term
                        | t==term = (Var v)
                        | otherwise = case term of
                            (Var x) ->  (Var x)
                            (Abst x e) -> Abst x (lightReverseBetaReduction t v e)
                            (Appl n m) -> Appl (lightReverseBetaReduction t v n) (lightReverseBetaReduction t v m)

mapSnd::(a -> b) -> (c, a) -> (c, b)
mapSnd f (a,b) = (a, f b)
tupAND::(Bool, (Bool, a)) -> (Bool, a)
tupAND (x,(y,z)) = (x && y, z)

runLambda::(Eq a, Show a) => (a->a) -> Lambda a -> Lambda a
runLambda rename l = snd.head $ dropWhile (fst) $ iterate (tupAND.(mapSnd $ betaReductionLMOM rename)) (fst $ betaReductionLMOM rename l, l)

--TODO: really inefficient
runDeBruj::DeBrujLambda -> DeBrujLambda
runDeBruj = lamToDeBruj.(runLambda succ).backToLambda

runDeBrujN::Int -> DeBrujLambda -> DeBrujLambda
runDeBrujN s t = remNames $ (iterate (snd.betaReductionLMOMDeBruj) (anyName t)) !! s

stepRepl::String -> IO()
stepRepl expr = do {
  t <- return $ lambdaFromString expr;
  putStrLn $ "read: "++(lambdaToBracketString t);
  stepRepl' t
}

stepReplD::DeBrujLambda -> IO()
stepReplD expr = do {
  t <- return $ backToLambda expr;
  putStrLn $ "read: "++(lambdaToBracketString' t);
  stepReplI t
}

stepReplI::Lambda Integer -> IO()
stepReplI expr = do {
  putStrLn $ lambdaToString' expr;
  --putStrLn $ lambdaToBracketString $ lambdaFromString expr;
  getChar;
  (comp, res) <- return $ ((betaReductionLMOM succ) expr);
  if comp then stepReplI res else putStrLn "halted."
}

stepRepl'::Lambda String -> IO ()
stepRepl' expr = do {
  putStrLn $ lambdaToString expr;
  --putStrLn $ lambdaToBracketString $ lambdaFromString expr;
  getChar;
  (comp, res) <- return $ ((betaReductionLMOM (++"'")) expr);
  if comp then stepRepl' res else putStrLn "halted."
}

{-
--Cannot be build with Haskell type system!
toFunction mapping (Var x) = fromJust $ lookup x mapping
toFunction mapping (Abst x lx) = (\y -> toFunction ((x,y):mapping) lx)
toFunction mapping (Appl n m) = (toFunction mapping n) (toFunction mapping m)
-}

debugLambdas::(Show a) => [Lambda a] -> IO ()
debugLambdas = putStrLn.unlines.(lambdaToString' <$>)
