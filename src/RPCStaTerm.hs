module RPCStaTerm(StaTerm(..), StaValue, subst, substs, fv, prTerm) where

import Data.List
import Term(Location(..),locToStr,seqToStr)

--
type StaValue = StaTerm -- Var x, Lam a xs m, Const i

data StaTerm = 
        Const Int
    | Var String
    | Lam Location [String] StaTerm 
    | Call StaValue  [StaValue]
    | Ret StaValue    -- New in StaTerm, not in EncTerm
    | Req StaValue [StaValue]
    | App StaValue [StaValue]
    | Let String StaTerm StaTerm 

--
subst :: StaTerm -> String -> StaValue -> StaTerm 
subst m@(Const i) x v = m
subst m@(Var y) x v = if x == y then v else m
subst m@(Lam loc xs mbody) x v = 
    let isin [] = False
        isin (y:ys) = x==y || isin ys 
    in  if isin xs then Lam loc xs mbody
        else Lam loc xs (subst mbody x v) 
subst m@(Call f ws) x v = Call (subst f x v) (map (\w -> subst w x v) ws)
subst m@(Ret w) x v = Ret (subst w x v)
subst m@(App f ws) x v = App (subst f x v) (map (\w -> subst w x v) ws) 
subst m@(Req f ws) x v = Req (subst f x v) (map (\w -> subst w x v) ws)
subst m@(Let y m1 m2) x v = 
    Let y (subst m1 x v) 
        (if x == y then m2 else subst m2 x v)

substs :: StaTerm -> [String] -> [StaValue] -> StaTerm 
substs m [] [] = m 
substs m (x:xs) (v:vs) = substs (subst m x v) xs vs 
substs m _ _ = error ("Error in substs: the lengths of vars and vals are different")

--
fv :: StaTerm -> [String]
fv m@(Const i) = []
fv m@(Var y) = [y]
fv m@(Lam loc xs mbody) = nub (fv mbody) \\ xs
fv m@(Call f ws) = nub (concat (map fv (f:ws)))
fv m@(Ret v) = fv v
fv m@(Req f ws) = nub (concat (map fv (f:ws)))
fv m@(App f ws) = nub (concat (map fv (f:ws)))
fv m@(Let x m1 m2) = nub (fv m1 `union` (nub (fv m2) \\ [x]))

--
prTerm :: StaTerm -> String 
prTerm (Const i) = show i 
prTerm (Var x) = x
prTerm (Lam loc xs m) = 
    "lam^" ++ locToStr loc ++ "(" ++ seqToStr xs ++ ")." ++ prTerm m
prTerm (App f ws) = 
    "(" ++ prTerm f ++ ") (" ++ seqToStr (map prTerm ws) ++ ")"
prTerm (Call f ws) = 
    "Call(" ++ prTerm f ++ ") (" ++ seqToStr (map prTerm ws) ++ ")"
prTerm (Ret w) =
    "Ret(" ++ prTerm w ++ ")"
prTerm (Req f ws) = 
    "Req(" ++ prTerm f ++ ") (" ++ seqToStr (map prTerm ws) ++ ")"
prTerm (Let x m1 m2) = 
    "let " ++ x ++ " = " ++ prTerm m1 ++ " in " ++ prTerm m2 

    
    