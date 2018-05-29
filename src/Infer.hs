module Infer(infer, inferRun) where

import Term as T
import TypedTerm as TT

infer :: Term -> TypedTerm
infer m = tym1
    where (tym, ty, equs, _) = genCst 1 m []
          equs1 = solve equs
          tym1 = substTerm tym equs1 

inferRun :: Term -> IO ()
inferRun m = do 
    let (tym, ty, equs, _) = genCst 1 m []
    let equs1 = solve equs
    let tym1 = substTerm tym equs1
    putStrLn (prTyTerm tym)
    mapM_ putStrLn (prEqus equs)
    putStrLn ""
    putStrLn (prTyTerm tym1)
    mapM_ putStrLn (prEqus equs1)
  
  --
data Equ = 
      EquTy TT.Type TT.Type 
    | EquLoc TT.TypedLocation TT.TypedLocation
    deriving Show

type Equations = [Equ]

prEqus :: Equations -> [String]
prEqus [] = []
prEqus ((EquTy (TT.VarType i) ty):equs) = 
    (show i ++ " = " ++ prTy ty) : prEqus equs
prEqus ((EquTy ty1 ty2):equs) =
    (prTy ty1 ++ " = " ++ prTy ty2) : prEqus equs 
prEqus ((EquLoc (TT.LocVarType i) tyloc):equs) = 
    (show i ++ " = " ++ prTyLoc tyloc) : prEqus equs
prEqus ((EquLoc tyloc1 tyloc2):equs) = 
    (prTyLoc tyloc1 ++ " = " ++ prTyLoc tyloc2) : prEqus equs 


--
substTerm :: TypedTerm -> Equations -> TypedTerm 
substTerm (TT.Const i) equs = TT.Const i
substTerm (TT.Var x) equs = TT.Var x 
substTerm (TT.Lam loc x ty m) equs =
    TT.Lam loc x (substTyEqus ty equs) (substTerm m equs )
substTerm (TT.App tyloc m1 m2) equs = 
    TT.App (substLocEqus tyloc equs)
        (substTerm m1 equs)
        (substTerm m2 equs)

substTyEqus ty [] = ty
substTyEqus ty ((EquTy (VarType i) ity):equs) =
    substTyEqus (subst ty i ity) equs 
substTyEqus ty ((EquLoc (LocVarType i) ilocty):equs) =
    substTyEqus (substTyTyLoc ty i ilocty) equs 

substLocEqus :: TypedLocation -> Equations -> TypedLocation
substLocEqus tyloc [] = tyloc 
substLocEqus tyloc (EquTy _ _:equs) = 
    substLocEqus tyloc equs  
substLocEqus tyloc (EquLoc (LocVarType i) ityloc:equs) = 
    substLocEqus (substTyLoc tyloc i ityloc) equs 

--
solve equs =
    let (equs1, changed1) = unifyEqus equs in
    let (equs2, changed2) = mergeAll equs1 in
    let (equs3, changed3) = propagate equs2 in 
    if changed1 || changed2 || changed3 then solve equs3
    else equs

--
propagate :: Equations -> (Equations, Bool)
propagate equs = propagate' equs equs

propagate' :: Equations -> Equations -> (Equations, Bool)
propagate' [] allequs = (allequs, False)
propagate' (EquTy (VarType i) ty:equs) allequs =
    let (allequs1, changed1) = propagateTy i ty allequs 
        (allequs2, changed2) = propagate' equs allequs1
    in  (allequs2, changed1 || changed2) 
propagate' (EquLoc (LocVarType i) locty:equs) allequs =
    let (allequs1, changed1) = propagateLoc i locty allequs 
        (allequs2, changed2) = propagate' equs allequs1
    in  (allequs2, changed1 || changed1)
propagate' (_:equs) allequs = 
    error ("Error in propagate': Not VarType nor LocVarType.")

propagateTy :: Int -> Type -> Equations -> (Equations, Bool)
propagateTy i ity [] = ([], False)
propagateTy i ity (EquTy varty ty:equs) = 
    let ty1 = subst ty i ity
        (equs1, changed1) = propagateTy i ity equs 
    in (EquTy varty ty1:equs1, ty1/=ty || changed1)
propagateTy i ity (EquLoc locvarty tyloc:equs) = 
    let (equs1, changed1) = propagateTy i ity equs 
    in (EquLoc locvarty tyloc:equs1, changed1)
    

propagateLoc :: Int -> TypedLocation -> Equations -> (Equations, Bool)
propagateLoc i ilocty [] = ([], False)
propagateLoc i ilocty (EquTy varty ty:equs) =
    let (equs1, changed1) = propagateLoc i ilocty equs
    in  (EquTy varty ty: equs1, changed1)
propagateLoc i ilocty (EquLoc locvarty tyloc:equs) =
    let tyloc1 = substTyLoc tyloc i ilocty 
        (equs1, changed1) = propagateLoc i ilocty equs 
    in  (EquLoc locvarty tyloc1:equs1, tyloc/=tyloc1 || changed1) 

mergeAll :: Equations -> (Equations, Bool)
mergeAll [] = ([], False)
mergeAll (equ:equs) = 
    let (equs1, therestequs1, changed1) = mergeTheRest equ equs 
        (equs2, changed2) = mergeAll therestequs1 
    in ([equ] ++ equs1 ++ equs2, changed1 || changed2)

mergeTheRest equbase [] = ([], [], False)
mergeTheRest equbase@(EquTy ty11 ty12) ((equ@(EquTy ty21 ty22)):equs) =
    let (equs2, therestequs2, changed2) = mergeTheRest equbase equs in
    if ty11 == ty21 then
        let (equs1, changed1) = unify (EquTy ty12 ty22) in
            (equs1 ++ equs2, therestequs2, changed1 || changed2) 
    else (equs2, equ:therestequs2, changed2)
mergeTheRest equbase@(EquLoc tyloc11 tyloc12) ((equ@(EquLoc tyloc21 tyloc22)):equs) =
    let (equs2,therestequs2,changed2) = mergeTheRest equbase equs in
    if tyloc11 == tyloc21 then
        let (equs1, changed1) = unify (EquLoc tyloc12 tyloc22) in 
            (equs1 ++ equs2, therestequs2, changed1 || changed2) 
    else (equs2, equ:therestequs2, changed2)
mergeTheRest equbase (equ:equs) = 
    let (equs1, therestequs1, changed) = mergeTheRest equbase equs in
        (equs1, equ:therestequs1, changed)

unifyEqus :: Equations -> (Equations, Bool)
unifyEqus [] = ([], False)
unifyEqus (equ:equs) =
    let (equ1,changed1) = unify equ 
        (equs2, changed2) = unifyEqus equs 
    in  (equ1 ++ equs2, changed1 || changed2)

unify :: Equ-> (Equations, Bool)
unify (EquTy ty1 ty2) = unify' ty1 ty2 
unify (EquLoc tyloc1 tyloc2) = unifyLoc' tyloc1 tyloc2 

unify' :: Type -> Type -> (Equations, Bool)
unify' IntType IntType = ([], False)
unify' ty1@IntType ty2@(VarType i) = ([EquTy ty2 ty1], True)
unify' ty1@IntType ty2@(FunType _ _ _ ) = unifyTyError ty1 ty2
unify' ty1@(VarType i) ty2 = ([EquTy ty1 ty2], False)
unify' ty1@(FunType _ _ _) ty2@IntType = unifyTyError ty1 ty2
unify' (FunType argty1 tyloc1 retty1) (FunType argty2 tyloc2 retty2) =
    let (argequ, argequchanged) = unify' argty1 argty2 
        (locequ, locequchanged) = unifyLoc' tyloc1 tyloc2 
        (retequ, retequchanged) = unify' retty1 retty2 
    in  (argequ ++ locequ ++ retequ, 
            argequchanged || locequchanged || retequchanged)
unify' ty1@(FunType argty tyloc retty) ty2@(VarType i) = ([EquTy ty2 ty1], True)

unifyLoc' :: TypedLocation -> TypedLocation -> (Equations, Bool) 
unifyLoc' tyloc1@(LocVarType i) tyloc2 = ([EquLoc tyloc1 tyloc2], False)
unifyLoc' tyloc1@(LocType loc) tyloc2@(LocVarType i) = 
    ([EquLoc tyloc2 tyloc1], True)
unifyLoc' tyloc1@(LocType loc1) tyloc2@(LocType loc2) = 
    if loc1 == loc2 then ([], True)
    else unifyLocError loc1 loc2

unifyTyError ty1 ty2 = 
    error (show ty1 ++ " not compatible with " ++ show ty2)

unifyLocError loc1 loc2 =
    error (show loc1 ++ " not compatible with " ++ show loc2)
--


--
type TyEnv = [(String, Type)]

genCst :: Int -> Term -> TyEnv -> (TypedTerm, Type, Equations, Int)
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
    where argty = VarType n1
          tyenv1 = (x,argty) : tyenv
          funty = FunType argty (LocType loc) bodyty
          (tym, bodyty, equ1, n1) = genCst n m tyenv1


tylookup :: String -> TyEnv -> Type
tylookup x tyenv =
    case tys of
        [] -> error ("lookup error: " ++ x ++ " " ++ show tyenv)
        (ty:_) -> ty 
    where
        tys = [ty | (y,ty) <- tyenv, x==y]



          

