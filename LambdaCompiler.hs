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

data LamFkt a b = Fkt (a -> b) | T b
data Lambda a = Variable a | Abstraction a (Lambda a) | Application (Lambda a) (Lambda a) deriving (Eq, Show)
instance (Arbitrary a) => Arbitrary (Lambda a) where
   arbitrary = sized arbitrarySizedLambda
arbitrarySizedLambda:: Arbitrary a => Int -> Gen (Lambda a)
arbitrarySizedLambda 0 = do{v <- arbitrary; return $ Variable v}
arbitrarySizedLambda s = do {
  c <- elements [0,1,2];
  case c of
    0 -> Variable <$> arbitrary;
    1 -> (Abstraction <$> arbitrary) <*> (arbitrarySizedLambda (pred s))
    2 -> do{
      v1 <- arbitrarySizedLambda (pred s);
      v2 <- arbitrarySizedLambda (pred s);
      return $ Application v1 v2}
}
data NamedDeBrujLambda a  = NBVariable Integer | NBAbstraction a (NamedDeBrujLambda a) | NBApplication (NamedDeBrujLambda a) (NamedDeBrujLambda a) deriving (Eq, Show)
data DeBrujLambda = BVariable Integer | BAbstraction (DeBrujLambda) | BApplication (DeBrujLambda) (DeBrujLambda) deriving (Eq, Show)

remNames::NamedDeBrujLambda a -> DeBrujLambda
remNames (NBVariable x) = BVariable x
remNames (NBAbstraction _ x) = BAbstraction (remNames x)
remNames (NBApplication m n) = BApplication (remNames m) (remNames n)

lamToDeBruj::(Eq a) => Lambda a -> DeBrujLambda
lamToDeBruj = remNames.lamToNamDeBruj

deBrujToString::DeBrujLambda -> String
deBrujToString = lambdaToString'.backToLambda

deBrujToBrString::DeBrujLambda -> String
deBrujToBrString = lambdaToBracketString'.backToLambda

backToLambda::DeBrujLambda -> Lambda Integer
backToLambda = (renameDubs succ).(backToLambda').(markByDepth [0..])

backToLambda'::NamedDeBrujLambda Integer -> Lambda Integer
backToLambda' (NBVariable x) = Variable x
backToLambda' (NBAbstraction n x) = Abstraction n (backToLambda' $ betaReductionDeBruj' 1 (NBVariable n) x) --TODO: doesn't work because of name clashes!
backToLambda' (NBApplication m n) = Application (backToLambda' m) (backToLambda' n)

markByDepth::[a] -> DeBrujLambda -> NamedDeBrujLambda a
markByDepth a (BVariable x) = NBVariable x
markByDepth (a:as) (BAbstraction x) = NBAbstraction a (markByDepth as x)
markByDepth a (BApplication m n) = NBApplication (markByDepth a m) (markByDepth a n)

infixl 9 <>
(<>)::Lambda a -> Lambda a -> Lambda a
(<>) a b = Application a b

varCont::Lambda a -> a
varCont (Variable a) = a

mapNames::(a->b) -> Lambda a-> Lambda b
mapNames f (Variable x) = Variable (f x)
mapNames f (Abstraction x lx) = Abstraction (f x) (mapNames f lx)
mapNames f (Application n m) = Application (mapNames f n) ( mapNames f m)

lambdaToString'::(Show a) => Lambda a -> String
lambdaToString' = lambdaToString.(mapNames show)
lambdaToString::Lambda String -> String
lambdaToString (Variable x)       = x
lambdaToString (Abstraction x lx@(Abstraction _ _)) = "/"++x++(lambdaToString lx)
lambdaToString (Abstraction x lx) = "/"++x++" "++(lambdaToString lx)
lambdaToString (Application n@(Abstraction _ _) m@(Abstraction _ _)) = "("++(lambdaToString n)++")"++"("++(lambdaToString m)++")"
--lambdaToString (Application n m@(Abstraction _ _)) = (lambdaToString n)++" ("++(lambdaToString m)++")"
lambdaToString (Application n@(Abstraction _ _) m@(Application _ _)) =  "("++(lambdaToString n)++") ("++(lambdaToString m)++")"
lambdaToString (Application n@(Application _ _) m@(Application _ _)) =  "("++(lambdaToString n)++") "++(lambdaToString m)
lambdaToString (Application n@(Abstraction _ _) m) = "("++(lambdaToString n)++")"++(lambdaToString m)
lambdaToString (Application n m@(Application _ _)) = (lambdaToString n)++" ("++(lambdaToString m)++")"
lambdaToString (Application n m@(Abstraction _ _)) = (lambdaToString n)++" ("++(lambdaToString m)++")"
lambdaToString (Application n m) = (lambdaToString n)++" "++(lambdaToString m)

testParser::Lambda Int -> Bool
testParser x = (lambdaFromString $ lambdaToString (modf x)) == (lambdaFromString $ lambdaToBracketString (modf x))
                          where modf = (mapNames show)

lambdaToTreeString l = lambdaToTreeString' l ""
lambdaToTreeString'::Lambda String -> String -> String
lambdaToTreeString' (Variable x) s       = s++x++"\n"
lambdaToTreeString' (Abstraction x lx) s = s++"/"++x++"\n"++(lambdaToTreeString' lx (s++"\t"))++"\n"
lambdaToTreeString' (Application n m)  s = s++"."++"\n"++(lambdaToTreeString' n (s))++(lambdaToTreeString' m (s))++"\n"

lambdaToBracketString'::(Show a) => Lambda a -> String
lambdaToBracketString' = lambdaToBracketString.(mapNames show)
lambdaToBracketString::Lambda String -> String
lambdaToBracketString (Variable x)       = x
lambdaToBracketString (Abstraction x lx) = "(/"++x++" "++(lambdaToBracketString lx)++")"
lambdaToBracketString (Application n m)  = "("++(lambdaToBracketString n)++" "++(lambdaToBracketString m)++")"

--(Abstraction 0 (Application (Abstraction 1 (Variable 1) ) (Variable 0)))

ls = lambdaFromString
lsd::String -> DeBrujLambda
lsd = lamToDeBruj.lambdaFromString
lsa::(Read a) => String -> Lambda a
lsa = (mapNames read).lambdaFromString
lambdaFromString::String -> Lambda String
lambdaFromString s = case parse parseLambda "" s of
                        Right a -> a
                        Left err -> error $ show err

parseLambda::Parsec String a (Lambda String)
parseLambda = (foldl1 Application) <$> (many1 parseSingleLambda)

parseSingleLambda::Parsec String a (Lambda String)
parseSingleLambda = skipSpace >> ((try $ parseAbstraction) <|> (try $ parseVar) <|> (paren parseLambda))

parseVar::Parsec String a (Lambda String)
parseVar = skipSpace >> (Variable <$> many1 (noneOf " /()"))
parseAbstraction::Parsec String a (Lambda String)
parseAbstraction = do{
                skipSpace >> (string"/");
                v <- parseVar;
                (Abstraction $ varCont v) <$> parseLambda}

exchangeFirstLeftAssoc::Lambda a -> Lambda a -> Lambda a
exchangeFirstLeftAssoc t (Application start@(Application _ _) end) = Application (exchangeFirstLeftAssoc t start) end
exchangeFirstLeftAssoc t x = Application t x

reverseAppAssoc::Lambda a -> Lambda a
reverseAppAssoc (Application x (Application y z)) = reverseAppAssoc $ Application (Application x y) z
reverseAppAssoc x = x

skipSpace::Parsec String a String
skipSpace = many $ oneOf " \t\n"
paren::Parsec String a b -> Parsec String a b
paren p = do{skipSpace; char '('; skipSpace; r <- p; skipSpace; char ')'; skipSpace; return r}


vars::(Eq a) => Lambda a -> [a]
vars (Variable x)       = [x]
vars (Abstraction _ lx) = vars lx
vars (Application x y)  = (vars x)++(vars y)

bounds::(Eq a ) => Lambda a -> [a]
bounds (Variable _)       = []
bounds (Abstraction x lx) = x:(bounds lx)
bounds (Application x y)  = (bounds x)++(bounds y)

unbounds::(Eq a) => Lambda a -> [a]
unbounds l = unbounds' l []

unbounds'::(Eq a) => Lambda a -> [a] -> [a]
unbounds' (Variable x)       acc = [x]\\acc
unbounds' (Abstraction x lx) acc = unbounds' lx (x:acc)
unbounds' (Application x y)  acc = union (unbounds' x acc) (unbounds' y acc)

lamToNamDeBruj::(Eq a) => Lambda a -> NamedDeBrujLambda a
lamToNamDeBruj l = lamToNamDeBruj' l (const 0) 0

--expression, naming function, depth
lamToNamDeBruj'::(Eq a) => Lambda a ->(a -> Integer) -> Integer -> NamedDeBrujLambda a
lamToNamDeBruj' (Variable x)       f d = NBVariable $ d - (f x)
lamToNamDeBruj' (Abstraction x lx) f d = NBAbstraction x $ lamToNamDeBruj' lx (\y -> if (y==x) then d else f y) (succ d)
lamToNamDeBruj' (Application n m)  f d = NBApplication (lamToNamDeBruj' n f d) (lamToNamDeBruj' m f d)

validifyUnbound::(Eq a)=> Lambda a -> Lambda a
validifyUnbound l = foldr Abstraction l (unbounds l)

renameDubs::(Eq a) => (a -> a) -> Lambda a -> Lambda a
renameDubs f = renameDubs' f []
renameDubs'::(Eq a) => (a -> a) -> [a] -> Lambda a -> Lambda a
renameDubs' f stack (Variable x)        = Variable x
renameDubs' f stack (Abstraction x lx)  = Abstraction x $ (renameDubs' f (x:stack)) $ searchAbstraction x lx (alphaReduction x x')
  where x' = (head $ dropWhile (flip elem $ (x:stack)) $ iterate f x)
renameDubs' f stack (Application n m)   = Application (renameDubs' f stack n) (renameDubs' f stack m)

--search for a certain abstraction binding the variable v
searchAbstraction::(Eq a) => a -> Lambda a -> (Lambda a -> Lambda a) -> Lambda a
searchAbstraction v a@(Variable x) f = a
searchAbstraction v a@(Abstraction x lx) f
                            |v==x = f a
                            |otherwise = Abstraction x (searchAbstraction v lx f)
searchAbstraction v (Application n m) f = Application (searchAbstraction v n f) (searchAbstraction v m f)

alphaReduction::(Eq a) => a -> a -> Lambda a -> Lambda a
alphaReduction a b (Variable c)
                |a==c = Variable b
                |otherwise = Variable c
alphaReduction a b (Abstraction c lx)
                |a==c = Abstraction b (alphaReduction a b lx)
                |otherwise = Abstraction c (alphaReduction a b lx)
alphaReduction a b (Application n m) = Application (alphaReduction a b n) (alphaReduction a b m)

exchangeVar::(Eq a) => a -> Lambda a -> Lambda a -> Lambda a
exchangeVar a t (Variable c)
                |a==c = t
                |otherwise = Variable c
exchangeVar a t (Abstraction c lx)
                |a==c = Abstraction c (exchangeVar a t lx)
                |otherwise = Abstraction c (exchangeVar a t lx)
exchangeVar a t (Application n m) = Application (exchangeVar a t n) (exchangeVar a t m)

--TODO: should be made deprecated
--beta reduction with renaming function. Returns additionally whether the term has halted (any computation has been done)
betaReductionLMOM::(Eq a) => (a->a) -> Lambda a -> (Bool, Lambda a)
betaReductionLMOM f (Application (Abstraction x e) y)
                                          | not comp = (True, renameDubs f $ exchangeVar x y e)
                                          | otherwise = (True, Application (Abstraction x res) y)
                              where (comp, res) = betaReductionLMOM f e
betaReductionLMOM f a@(Application m n)
                                          | compM = (True, Application m' n)
                                          | compN = (True, Application m n')
                                          | otherwise = (False, a)
                              where (compM, m') = betaReductionLMOM f m
                                    (compN, n') = betaReductionLMOM f n
betaReductionLMOM f (Abstraction x e) = (comp, Abstraction x res)
                              where (comp, res) = (betaReductionLMOM f e)
betaReductionLMOM _ x = (False, x)

--assumes DeBrujin normal form (no renaming required). Names still kept for convenience
betaReductionLMOMDeBruj::(Eq a) => NamedDeBrujLambda a -> (Bool, NamedDeBrujLambda a)
betaReductionLMOMDeBruj (NBApplication (NBAbstraction x e) y)
                                          | not comp = (True, betaReductionDeBruj' 1 y e) --1 because we already jumped into one abstraction
                                          | otherwise = (True, NBApplication (NBAbstraction x res) y)
                              where (comp, res) = betaReductionLMOMDeBruj e
betaReductionLMOMDeBruj a@(NBApplication m n)
                                          | compM = (True, NBApplication m' n)
                                          | compN = (True, NBApplication m n')
                                          | otherwise = (False, a)
                              where (compM, m') = betaReductionLMOMDeBruj m
                                    (compN, n') = betaReductionLMOMDeBruj n
betaReductionLMOMDeBruj (NBAbstraction x e) = (comp, NBAbstraction x res)
                              where (comp, res) = (betaReductionLMOMDeBruj e)
betaReductionLMOMDeBruj x = (False, x)


betaReductionDeBruj'::(Eq a) => Integer -> NamedDeBrujLambda a -> NamedDeBrujLambda a -> NamedDeBrujLambda a
betaReductionDeBruj' i t a@(NBVariable x)
                            | i == x = t
                            | otherwise = a
betaReductionDeBruj' i t (NBAbstraction n m) = NBAbstraction n (betaReductionDeBruj' (succ i) t m)
betaReductionDeBruj' i t (NBApplication n m) = NBApplication (betaReductionDeBruj' i t n) (betaReductionDeBruj' i t m)

mapSnd::(a -> b) -> (c, a) -> (c, b)
mapSnd f (a,b) = (a, f b)
tupAND::(Bool, (Bool, a)) -> (Bool, a)
tupAND (x,(y,z)) = (x && y, z)

runLambda::(Eq a) => (a->a) -> Lambda a -> Lambda a
runLambda rename l = snd.head $ dropWhile (fst) $ iterate (tupAND.(mapSnd $ betaReductionLMOM rename)) (fst $ betaReductionLMOM rename l, l)

runDeBruj::DeBrujLambda -> DeBrujLambda
runDeBruj = lamToDeBruj.(runLambda succ).backToLambda

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
toFunction mapping (Variable x) = fromJust $ lookup x mapping
toFunction mapping (Abstraction x lx) = (\y -> toFunction ((x,y):mapping) lx)
toFunction mapping (Application n m) = (toFunction mapping n) (toFunction mapping m)
-}
