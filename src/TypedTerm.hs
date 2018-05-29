module TypedTerm (
  TypedLocation(..),
  Type(..),
  TypedTerm(..), 
  subst, substTyTyLoc, substTyLoc,
  prTyTerm, prTy, prTyLoc) where

import Term(Location(..))

data TypedLocation = 
    LocVarType Int 
  | LocType Location 
  deriving (Show,Eq) 

data Type =
    IntType
  | VarType Int
  | FunType Type TypedLocation Type
  deriving (Show,Eq) 

data TypedTerm = 
    Const Int 
  | Var String 
  | Lam Location String Type TypedTerm 
  | App TypedLocation TypedTerm TypedTerm

subst :: Type -> Int -> Type -> Type
subst IntType i ty = IntType
subst (VarType j) i ty =
  if i == j then ty else VarType j
subst (FunType argty tyloc retty) i ty = 
  FunType (subst argty i ty) tyloc (subst retty i ty)

substTyTyLoc :: Type -> Int -> TypedLocation -> Type
substTyTyLoc IntType i tyloc = IntType 
substTyTyLoc (VarType j) i tyloc = VarType j
substTyTyLoc ty@(FunType argty (LocType loc) retty) i tyloc = ty
substTyTyLoc ty@(FunType argty (LocVarType j) retty) i tyloc =
  FunType argty tyloc retty

substTyLoc :: TypedLocation -> Int -> TypedLocation -> TypedLocation 
substTyLoc tyloc@(LocVarType i) j jtyloc = 
  if i == j then jtyloc else tyloc
substTyLoc tyloc@(LocType loc) j jtyplcoc = tyloc

prTyTerm :: TypedTerm -> String
prTyTerm (Var x) = x
prTyTerm (Lam Client x ty n) = 
    "lam^c (" ++ x ++ ":" ++ prTy ty ++ "). " ++ prTyTerm n
prTyTerm (Lam Server x ty n) = 
    "lam^s (" ++ x ++ ":" ++ prTy ty ++ "). " ++ prTyTerm n
prTyTerm (App tyloc l n) = 
    "(" ++ prTyTerm l ++ ") "++ 
    prTyLoc tyloc ++
    " (" ++ prTyTerm n ++ ")"
prTyTerm (Const i) = show i

prTy :: Type -> String
prTy IntType = "int"
prTy (VarType i) = "a" ++ show i
prTy (FunType argty tyloc retty) = 
  "(" ++ prTy argty ++ "-" ++ prTyLoc tyloc ++ "->" ++ prTy retty ++ ")"

prTyLoc :: TypedLocation -> String 
prTyLoc (LocVarType i) = "l" ++ show i 
prTyLoc (LocType Client) = "c"
prTyLoc (LocType Server) = "s"