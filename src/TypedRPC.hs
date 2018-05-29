module TypedRPC where

import Term (Term, Location(..), prTerm)
import TypedTerm
import Infer(infer)

elaborate :: Term -> TypedTerm
elaborate m = infer m 

runElaborate m = do 
    let tym = elaborate m 
    putStrLn (prTerm m)
    putStrLn " is elaborated to "
    putStrLn (prTyTerm tym)

