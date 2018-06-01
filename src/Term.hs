module Term where

-- a,b :: client | server
data Location = Client | Server deriving (Show, Eq)


-- L,M,N :: = V | L M
-- V ::= x | lam^a x.M
data Term = Const Int | Var String | Lam Location String Term | App Term Term

type Value = Term     -- Var or Lam

prTerm :: Term -> String
prTerm (Var x) = x
prTerm (Lam loc x n) = "lam^" ++ locToStr loc ++  " " ++ x ++ ". " ++ prTerm n
prTerm (App l n) = "(" ++ prTerm l ++ ") "++ "(" ++ prTerm n ++ ")"
prTerm (Const i) = show i

locToStr Client = "c"
locToStr Server = "s"

seqToStr [] = ""
seqToStr [x] = x
seqToStr (x:xs) = x ++ "," ++ seqToStr xs

