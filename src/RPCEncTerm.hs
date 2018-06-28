module RPCEncTerm(EncTerm(..), EncValue, subst, substs, prTerm) where


import Term(Location(..),locToStr,seqToStr)

--
type EncValue = EncTerm -- Var x, Lam a xs m, Const i

data EncTerm = 
      Const Int
    | Var String
    | Lam Location [String] EncTerm 
    | Call EncValue  [EncValue]
    | Req EncValue [EncValue]
    | App EncValue [EncValue]
    | Let String EncTerm EncTerm 
    -- | LetApp String EncValue [EncValue] EncTerm 
    -- | LetReq String EncValue [EncValue] EncTerm 

--
subst :: EncTerm -> String -> EncValue -> EncTerm 
subst m@(Const i) x v = m
subst m@(Var y) x v = if x == y then v else m
subst m@(Lam loc xs mbody) x v = 
    let isin [] = False
        isin (y:ys) = x==y || isin ys 
    in  if isin xs then Lam loc xs mbody
        else Lam loc xs (subst mbody x v) 
subst m@(Call f ws) x v = Call (subst f x v) (map (\w -> subst w x v) ws)
subst m@(App f ws) x v = App (subst f x v) (map (\w -> subst w x v) ws) 
subst m@(Req f ws) x v = Req (subst f x v) (map (\w -> subst w x v) ws)
subst m@(Let y m1 m2) x v = 
    Let y (subst m1 x v) 
        (if x == y then m2 else subst m2 x v)

substs :: EncTerm -> [String] -> [EncValue] -> EncTerm 
substs m [] [] = m 
substs m (x:xs) (v:vs) = substs (subst m x v) xs vs 
substs m _ _ = error ("Error in substs: the lengths of vars and vals are different")

--
prTerm :: EncTerm -> String 
prTerm (Const i) = show i 
prTerm (Var x) = x
prTerm (Lam loc xs m) = 
    "lam^" ++ locToStr loc ++ "(" ++ seqToStr xs ++ ")." ++ prTerm m
prTerm (App f ws) = 
    "(" ++ prTerm f ++ ") (" ++ seqToStr (map prTerm ws) ++ ")"
prTerm (Call f ws) = 
    "Call(" ++ prTerm f ++ ") (" ++ seqToStr (map prTerm ws) ++ ")"
prTerm (Req f ws) = 
    "Req(" ++ prTerm f ++ ") (" ++ seqToStr (map prTerm ws) ++ ")"
prTerm (Let x m1 m2) = 
    "let " ++ x ++ " = " ++ prTerm m1 ++ " in " ++ prTerm m2 


