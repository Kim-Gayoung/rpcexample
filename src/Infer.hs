module Infer where

import Term as T
import TypedTerm as TT

infer :: Term -> TypedTerm
infer m = tym
    where (tym, ty, equ, _) = genCst 1 m []

--
type Equation = [Equ]

data Equ = EquTy TT.Type TT.Type | EquLoc TT.TypedLocation TT.TypedLocation



--
type TyEnv = [(String, Type)]

genCst :: Int -> Term -> TyEnv -> (TypedTerm, Type, Equation, Int)
genCst n (T.Const i) tyenv = (TT.Const i, IntType, [], n)

genCst n (T.Var x) tyenv = (TT.Var x, ty, [], n)
    where ty = tylookup x tyenv

genCst n (T.App m1 m2) tyenv = (TT.App locvar tym1 tym2, retty, equ, n2+2)
    where (tym1, ty1, equ1, n1) = genCst n m1 tyenv 
          (tym2, ty2, equ2, n2) = genCst n1 m2 tyenv 
          locvar = LocVarType n2
          retty = VarType (n2+1)
          equ = equ1 ++ equ2 ++ [EquTy ty1 (FunType ty2 locvar retty)]

genCst n (T.Lam loc x m) tyenv = (TT.Lam loc x argty tym, funty, equ1, n1+1)
    where tyenv1 = (x,argty) : tyenv
          argty = VarType n1
          funty = FunType argty (LocType loc) bodyty
          (tym, bodyty, equ1, n1) = genCst n m tyenv1


tylookup :: String -> TyEnv -> Type
tylookup x tyenv =
    case tys of
        [] -> error ("lookup error: " ++ x ++ " " ++ show tyenv)
        (ty:_) -> ty 
    where
        tys = [ty | (x,ty) <- tyenv]



          

