module RPC where

import Term 

run = putStrLn $ prTerm $ eval ex1 Client

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

prTerm :: Term -> String
prTerm (Var x) = x
prTerm (Lam Client x n) = "lam^c " ++ x ++ ". " ++ prTerm n
prTerm (Lam Server x n) = "lam^s " ++ x ++ ". " ++ prTerm n
prTerm (App l n) = "(" ++ prTerm l ++ ") "++ "(" ++ prTerm n ++ ")"
prTerm (Const i) = show i

--
ex1Left = Lam Server "f" 
        (App (Lam Server "x" (Var "x")) 
            (App (Var "f") (Const 1)))
ex1Right = Lam Client "y"
        (App (Lam Server "z" (Var "z")) (Var "y"))

ex1 = App ex1Left ex1Right










