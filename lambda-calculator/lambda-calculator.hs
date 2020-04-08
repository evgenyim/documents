import Data.List (union, (\\))
import Data.Maybe

type Symb = String 

infixl 2 :@
infix 1 `betaEq`, `alphaEq`

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq)

instance Show Expr where
    show (Var a) = a
    show (Var a :@ Var b) = a ++ " " ++ b
    show (a :@ Var b) = "(" ++ show a ++ ") " ++ b
    show (Var a :@ b) = a ++ " (" ++ show b ++ ")"
    show (a :@ b) = "(" ++ show a ++ ") (" ++ show b ++ ")" 
    show (Lam x e) = "\\" ++ x ++ " -> " ++ show e 

instance Read Expr where
    readsPrec _ s = [(parse s,"")]

flex :: String -> String
flex s = fst $ head $ lex s

slex :: String -> String
slex s = snd $ head $ lex s

befB :: String -> Int -> String
befB s 0 = []
befB (s:ss) n = if s == '(' then s:(befB ss (n+1))
                else if s == ')' && n == 1 then []
                else if s == ')' then s:(befB ss (n-1))
                else s:(befB ss n)

remB :: String -> Int -> String
remB s 0 = s
remB (s:ss) n = if s == '(' then remB ss (n+1)
                else if s == ')' then remB ss (n-1)
                else remB ss n 

parseTerm :: String -> Expr
parseTerm s = if flex s == "\\" then parseLam $ slex s
              else foldl1 (:@) (helper s) where
                helper [] = []
                helper s = if flex s == "(" then [parseTerm $ befB (slex s) 1] ++ pt
                           else if flex s == ")" then []
                           else (Var (flex s)) : (helper $ slex s) where
                                    pt = if remB (slex s) 1 /= "" then [parseTerm $ remB (slex s) 1]
                                          else []

parse :: String -> Expr
parse s = parseTerm s

parseLam :: String -> Expr
parseLam s = if flex s == "->" then parseTerm $ slex s
             else Lam (flex s) (parseLam $ slex s)


freeVars :: Expr -> [Symb] 
freeVars (Var n) = [n] 
freeVars (e1 :@ e2) = union (freeVars e1) (freeVars e2) 
freeVars (Lam n e) = (freeVars e) \\ [n] 

subst :: Symb -> Expr -> Expr -> Expr 
subst v' n' m = subst' m where
                subst' (Var m) = if m == v' then n' 
                                 else Var m
                subst' (e1 :@ e2) = (subst' e1) :@ (subst' e2)
                subst' (Lam n e) = if n == v' then Lam n e
                                   else if n `notElem` fv then Lam n (subst' e)
                                   else Lam n1 (subst' e1) where
                                        fv = freeVars n'
                                        n1 = newVar n (fv `union` freeVars e)
                                        e1 = subVar n n1 e

subVar :: Symb -> Symb -> Expr -> Expr 
subVar s s' e = subst s (Var s') e

newVar :: Symb -> [Symb] -> Symb
newVar j js = if j `elem` js then newVar (j ++ "'") js
               else j

alphaEq :: Expr -> Expr -> Bool
alphaEq (Var n) (Var m) = n == m
alphaEq (e1 :@ e2) (c1 :@ c2) = (alphaEq e1 c1) && (alphaEq e2 c2)
alphaEq (Lam n e1) (Lam m e2) = if n == m then alphaEq e1 e2
                                else (alphaEq e1 (subst m (Var n) e2)) && (alphaEq (e2) (subst n (Var m) e1))
alphaEq _ _ = False

reduceOnce :: Expr -> Maybe Expr
reduceOnce ((Lam n e) :@ t) = Just $ subst n t e
reduceOnce (Lam n e) = if r == Nothing then Nothing
                       else Just $ Lam n (fromJust $ r) where
                                        r = reduceOnce e
reduceOnce (Var n) = Nothing
reduceOnce (e1 :@ e2) = if r1 /= Nothing then Just $ (fromJust $ r1) :@ e2
                        else if r2 /= Nothing then Just $ e1 :@ (fromJust $ r2)
                        else Nothing where 
                                        r1 = reduceOnce e1
                                        r2 = reduceOnce e2

nf :: Expr -> Expr 
nf e = if r /= Nothing then nf (fromJust $ r)
       else e where r = reduceOnce e

betaEq :: Expr -> Expr -> Bool 
betaEq e1 e2 = nf e1 `alphaEq` nf e2 
