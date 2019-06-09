module SATSearch where

import Text.Parsec hiding (spaces)
import Data.Maybe
import Control.Monad


data Term a = Split (Term a) (Term a) | Atom a | BOT deriving (Eq, Show)
data HKB a = CKB [[HKB a]] | KBT (KB a)
type KB a = [[Term a]]

--------------------------------------------------
--Parsing
--------------------------------------------------

reservedChar = " \n\t()"

spaces1::Parsec String st String
spaces1 = (many1 $ oneOf " \n\t")

spaces::Parsec String st String
spaces = (many $ oneOf " \n\t")

idfr::Parsec String st String
idfr = many1 $ noneOf reservedChar

term::Parsec String st (Term String)
term = spaces >> termSeq <* spaces

bracTerm::Parsec String st (Term String)
bracTerm = char '(' >> term <* char ')'

termSeq::Parsec String st (Term String)
termSeq = (foldl1 Split) <$> (sepBy ((Atom <$> idfr) <|> bracTerm <|> (return BOT)) spaces1)

vartermFit::(Eq a) => [a] -> Term a -> Term a -> Maybe [(a,Term a)]
vartermFit vars (Atom a) y
  | a `elem` vars = Just [(a,y)]
  | otherwise = case y of
                  (Atom c) -> if c==a then Just [] else Nothing
                  x -> Nothing
vartermFit vars (Split x y) (Split x' y') = do{a<-(vartermFit vars x x'); b<- (vartermFit vars y y'); return $ a++b}
vartermFit _ _ _ = Nothing

applyFit::(Eq a) => Term a -> [(a,Term a)] -> Term a
applyFit BOT _ = BOT
applyFit (Atom a) lst = case lookup a lst of
                          Just t -> t
                          Nothing -> Atom a
applyFit (Split x y) lst = Split (applyFit x lst) (applyFit y lst)

-- a b makes the rule, that is applied to c into a term d
ruleAppl::(Eq a) => [a] -> Term a -> Term a -> Term a -> Maybe (Term a)
ruleAppl vars a b c = (applyFit b) <$> (vartermFit vars a c)

foldRuleAppl::(Eq a) =>  [a] -> Term a -> Term a -> Term a -> Term a
foldRuleAppl _ _ _ (BOT) = BOT
foldRuleAppl vars a b at@(Atom c) = case ruleAppl vars a b at of
                                        Just t -> t
                                        Nothing -> at
foldRuleAppl vars a b s@(Split x y) = case ruleAppl vars a b tterm of
                                        Just t -> t
                                        Nothing -> s
                                where tterm = Split (foldRuleAppl vars a b x) (foldRuleAppl vars a b y)

leftAssocLst = reverse.leftAssocLst'
leftAssocLst'::Term a -> [Term a]
leftAssocLst' BOT = [BOT]
leftAssocLst' (Atom a) = [(Atom a)]
leftAssocLst' (Split x y) = y:(leftAssocLst' x)

termToKB::(Eq a) => a -> a -> Term a -> KB a
termToKB impl conj a@(Split(Split (Atom i) x ) y)
  | impl == i = map (x:) (termToKB impl conj y)
  | conj == i = (termToKB impl conj x) ++ (termToKB impl conj y)
  | otherwise = [[a]]
termToKB _ _ x = [[x]]

transformInfixOp::(Eq a) => [a] -> a -> Term a -> Term a
transformInfixOp vars@(x:y:zs) op = foldRuleAppl vars (Split(Split (Atom x) (Atom op)) (Atom y)) (Split(Split (Atom op) (Atom x)) (Atom y))
transformPostfixOp::(Eq a) => [a] -> a -> Term a -> Term a
transformPostfixOp vars@(x:y:zs) op = foldRuleAppl vars (Split (Atom x) (Atom op)) (Split (Atom op) (Atom x))

removeLastBOT::KB a -> KB a
removeLastBOT kb = case last kb of
                    [BOT] -> init kb
                    x -> kb

kbFromFile::String -> IO (KB String)
kbFromFile filename = do{
  s <- readFile filename;
  case parse term filename s of
    Right t -> return $ removeLastBOT $ termToKB "->" "." $ transformPostfixOp ["x","y"] "." $ transformInfixOp ["x","y"] "->" $ t;
    Left err -> fail (show err);
}
