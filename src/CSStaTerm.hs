module CSStaTerm(StaTerm(..), StaValue, subst, substs, prTerm, FunStore, ClosedFun) where

import Term(Location(..),locToStr,seqToStr)

--
type StaValue = StaTerm -- Var x, Clo f vs, Const i

data StaTerm = 
      Const Int
    | Var String
    | Clo String [StaValue]
    | Call StaValue  [StaValue]
    | Ret StaValue    -- New in StaTerm, not in EncTerm
    | Req StaValue [StaValue]
    | App StaValue [StaValue]
    | Let String StaTerm StaTerm 

-- z1..zk lam^a (x1..xn).m
type ClosedFun = ([String], Location, [String], StaTerm) -- No Clo f vs in StaTerm
type FunStore = [(String, ClosedFun)]

--
subst :: StaTerm -> String -> StaValue -> StaTerm 
subst m@(Const i) x v = m
subst m@(Var y) x v = if x == y then v else m
subst m@(Clo f vs) x v = Clo f (map (\w -> subst w x v) vs)
--    error ("subst on Clo: " ++ prTerm m ++ " " ++ x ++ " " ++ prTerm v)
-- subst m@(Lam loc xs mbody) x v = 
--     let isin [] = False
--         isin (y:ys) = x==y || isin ys 
--     in  if isin xs then Lam loc xs mbody
--         else Lam loc xs (subst mbody x v) 
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
prTerm :: StaTerm -> String 
prTerm (Const i) = show i 
prTerm (Var x) = x
prTerm (Clo f vs) =
    "Clo(" ++ f ++ ", " ++ seqToStr (map prTerm vs) ++ ")"
-- prTerm (Lam loc xs m) = 
--     "lam^" ++ locToStr loc ++ "(" ++ seqToStr xs ++ ")." ++ prTerm m
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
    
        
        