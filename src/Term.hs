module Term where

-- a,b :: client | server
data Location = Client | Server deriving Show


-- L,M,N :: = V | L M
-- V ::= x | lam^a x.M
data Term = Const Int | Var String | Lam Location String Term | App Term Term

type Value = Term     -- Var or Lam

