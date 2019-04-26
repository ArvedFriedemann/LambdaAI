module CellularAutomata where

import Text.Parsec
import Control.Monad
import Data.List

data Term a = Var a | Atom a | Split (Term a) (Term a) deriving (Show, Eq)


matching::(Eq a) => Term a -> Term a -> Maybe [(a,Term a)]
matching (Var x) y = Just [(x,y)]
matching (Split x y) (Split x' y') = do {
  lm <- matching x x';
  rm <- matching y y';
  guard $ and [(a==a')==>(b==b') | (a,b)<-lm, (a',b')<-rm];
  return $ nub $ lm++rm;
}
matching (Atom x) (Atom x')
  | x==x' = Just []
  | otherwise = Nothing
matching _ _ = Nothing

applyMatch::(Eq a) => Term a -> [(a, Term a)] -> Term a
applyMatch a@(Atom x)   m = a
applyMatch v@(Var x)    m = case lookup x m of
                              Just t -> t
                              Nothing -> v
applyMatch (Split x y)  m = Split (applyMatch x m) (applyMatch y m)

--apply rule a=b on c
apply::(Eq a) => Term a -> Term a -> Term a -> Maybe (Term a)
apply a b c = (applyMatch b) <$> (matching a c)


---------------------------------------
--parsing
---------------------------------------
sepChar = ['\t','\n',' ']
separators = symbol <$> return <$> sepChar
parOn = symbol "("
parOff = symbol ")"
quoteSymb = '`'
ruleEnd = symbol ";"
ruleInterm = symbol "="
quoteLst = [quoteSymb]
quoteOn = spaces >> string quoteLst
quoteOff = string quoteLst >> spaces >> return quoteLst
fixedSymbols = [ruleInterm, ruleEnd]++separators++[parOn,parOff,quoteOn,quoteOff]

symbol::String -> Parsec String st String
symbol s = do{spaces; s' <- string s; spaces; return s'}

formatSymbs::Parsec String st String
formatSymbs = many $ oneOf sepChar

sentences::Parsec String st [(Term String, Term String)]
sentences = many $ do {
  a <- term;
  ruleInterm;
  b <- term;
  spaces;
  choice [choice [void newline, void ruleEnd], eof];
  return (a,b)
}

term::Parsec String st (Term String)
term = leftAssocTerm <$> (endBy1 (choice [between parOn parOff term, name]) (spaces) )

leftAssocTerm::[Term a] -> Term a
leftAssocTerm ts = foldl1 Split ts

name::Parsec String st (Term String)
name = (choice [variable, atom])

atom::Parsec String st (Term String)
atom = Atom <$> (choice [between quoteOn quoteOff (many1 $ noneOf quoteLst),
                        many1 $ none (noneOf sepChar) fixedSymbols])

variable::Parsec String st (Term String)
variable = Var <$> do {
  x <- choice [upper, char '_'];
  xs <- many $ none (noneOf sepChar) fixedSymbols;
  return $ x:xs
}

none:: (Stream s m t, Show a) => ParsecT s u m b -> [ParsecT s u m a] -> ParsecT s u m b
none p lst = (notFollowedBy $ try $ choice lst) >> p



termFromString::String -> Term String
termFromString s = case parse term "" s of
                        Right a -> a
                        Left err -> error $ show err

kbFromString::String -> [(Term String, Term String)]
kbFromString s = case parse sentences "" s of
                        Right a -> a
                        Left err -> error $ show err

---------------------------------------
--util
---------------------------------------
(==>)::Bool -> Bool -> Bool
(==>) True False = False
(==>) _ _ = True
