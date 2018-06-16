module CompStaTerm where

import Term(Location(..))
import TypedTerm as TT 
import StaTerm as ST 

-- Compilation for Client
compStaTerm :: TypedTerm -> StaTerm
compStaTerm m = ST.Const 0


compClient :: Int -> TypedTerm -> (Int, StaTerm) 
compClient i m = (i, ST.Const 0)


-- Compilation for Server
compServer :: Int -> TypedTerm -> (Int, StaTerm)
compServer i m = (i, ST.Const 0)




