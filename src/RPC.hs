module RPC where

import Term 

-- The RPC calculus
-- Syntax

-- => Term.hs

-- Eval

eval :: Term -> Location -> Value
eval (Lam b x m) a = Lam b x m
-- eval (Var x) = (Var x)   -- Impossible in the top-level
eval (App l m) a =
    let Lam b x n = eval l a in 
    let w = eval m a in
    let v = eval (subst n x w) b in v
eval (Const i) a = Const i

subst :: Term -> String -> Value -> Term
subst (Var x) y w = if x == y then w else Var x
subst (Lam b x m) y w = 
    if x == y then Lam b x m
    else Lam b x (subst m y w)
subst (App l n) y w = App (subst l y w) (subst n y w)
subst (Const i) y w = Const i











