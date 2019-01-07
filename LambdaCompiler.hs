module LambdaCompiler where

import Text.Parsec
import Text.Parsec.Char
import Data.List
import Data.Either
import Debug.Trace
import Text.Parsec.Token

data Lambda a             = Variable a        | Abstraction a (Lambda a)             | Application (Lambda a) (Lambda a) deriving (Eq, Show)
data NamedDeBrujLambda a  = BVariable Integer | BAbstraction a (NamedDeBrujLambda a) | BApplication (NamedDeBrujLambda a) (NamedDeBrujLambda a) deriving (Eq, Show)

--data DeBrujLambda        = BVariable Integer | BAbstraction DeBrujLambda   | BApplication DeBrujLambda DeBrujLambda deriving (Eq, Show)

varCont::Lambda a -> a
varCont (Variable a) = a

lambdaToString::Lambda String -> String
lambdaToString (Variable x)       = x
lambdaToString (Abstraction x lx@(Abstraction _ _)) = "/"++x++(lambdaToString lx)
lambdaToString (Abstraction x lx) = "/"++x++" "++(lambdaToString lx)
lambdaToString (Application n m@(Application _ _)) = (lambdaToString n)++" ("++(lambdaToString m)++")"
--lambdaToString (Application n@(Abstraction _ _) m@(Abstraction _ _)) = "("++(lambdaToString n)++")"++" ("++(lambdaToString m)++")"
--lambdaToString (Application n m@(Abstraction _ _)) = (lambdaToString n)++" ("++(lambdaToString m)++")"
lambdaToString (Application n@(Abstraction _ _) m) = "("++(lambdaToString n)++")"++(lambdaToString m)
lambdaToString (Application n m) = (lambdaToString n)++" "++(lambdaToString m)

lambdaFromString::String -> Lambda String
lambdaFromString s = case parse parseLambda "" s of
                        Right a -> a
                        Left err -> error $ show err

parseLambda::Parsec String a (Lambda String)
parseLambda = skipSpace >> ((try $ reverseAppAssoc <$> parseApplication) <|> (try $ parseAbstraction) <|> (try $ parseVar) <|> (paren parseLambda))
parseVar::Parsec String a (Lambda String)
parseVar = skipSpace >> (Variable <$> many1 (noneOf " /()"))
parseAbstraction::Parsec String a (Lambda String)
parseAbstraction = do{
                skipSpace >> (string"/");
                v <- parseVar;
                (Abstraction $ varCont v) <$> parseLambda}
parseApplication::Parsec String a (Lambda String)
parseApplication = do{
                e1 <- (try $ paren parseLambda) <|> (parseVar);
                skipSpace;
                e2 <- (try $ parseApplication) <|> (try $ paren parseLambda) <|> (try $ parseAbstraction) <|> (parseVar);
                return $ Application e1 e2
                }

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

lamToDeBruj::(Show a, Eq a) => Lambda a -> NamedDeBrujLambda a
lamToDeBruj l = lamToDeBruj' l (const 0) 0

--expression, naming function, depth
lamToDeBruj'::(Show a, Eq a) => Lambda a ->(a -> Integer) -> Integer -> NamedDeBrujLambda a
lamToDeBruj' (Variable x)       f d = BVariable $ d - (f x)
lamToDeBruj' (Abstraction x lx) f d = BAbstraction x $ lamToDeBruj' lx (\y -> if (y==x) then d else f y) (succ d)
lamToDeBruj' (Application n m)  f d = BApplication (lamToDeBruj' n f d) (lamToDeBruj' m f d)

validifyUnbound::(Eq a)=> Lambda a -> Lambda a
validifyUnbound l = foldr Abstraction l (unbounds l)

renameDubs::(Eq a) => [a] -> Lambda [a] -> Lambda [a]
renameDubs b (Variable x)        = Variable x
renameDubs b (Abstraction x lx)  = Abstraction x $ (renameDubs b) $ searchAbstraction x lx (alphaReduction x (x++b))
renameDubs b (Application n m)   = Application (renameDubs b n) (renameDubs b m)

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

--beta reduction with renaming suffix
betaReduction::(Eq a) => [a] -> Lambda [a] -> Lambda [a]
betaReduction s (Application (Abstraction x e) y) = renameDubs s $ exchangeVar x (betaReduction s y) e
betaReduction s (Application m n) = Application (betaReduction s m) (betaReduction s n)
betaReduction s (Abstraction x e) = Abstraction x (betaReduction s e)
betaReduction _ x = x


stepRepl::String -> IO ()
stepRepl expr = do {
  putStrLn expr;
  getChar;
  stepRepl (lambdaToString $ (betaReduction "'") $ lambdaFromString expr)
}
--BUG: stepRepl "(/f (/g f(g g)) (/g f(g g)) ) (/f a f)"
--should terminate
