module TypedTerm (TypedLocation(..),Type(..),TypedTerm(..)) where

import Term

data TypedLocation = 
    LocVarType Int 
  | LocType Location 
  deriving Show 

data Type =
    IntType
  | VarType Int
  | FunType Type TypedLocation Type
  deriving Show 

data TypedTerm = 
    Const Int 
  | Var String 
  | Lam Location String Type TypedTerm 
  | App TypedLocation TypedTerm TypedTerm

