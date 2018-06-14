module CompEncTerm where

import Term(Location(..))
import TypedTerm as TT 
import EncTerm as ET 

-- Compilation for Client
compEncTerm :: TypedTerm -> EncTerm
compEncTerm tt = snd (compClient 1 tt)

compClient :: Int -> TypedTerm -> (Int, EncTerm) 
compClient i (TT.Const c) = (i, ET.Const c)
compClient i (TT.Var x) = (i, ET.Var x)
compClient i (TT.Lam Client x ty m) = 
    let (j, m') = compClient i m 
    in  (j, ET.Lam Client [x] m')
compClient i (TT.Lam Server x ty m) = 
    let kvar = "k" ++ show i 
        k = ET.Var kvar
        (j, encm) = compServer (i + 1) m k 
    in  (j, ET.Lam Server [x, kvar] encm)
compClient i (TT.App (TT.LocType Client) fn arg) = 
    let fvar = "f" ++ show i 
        xvar = "x" ++ show (i+1) 
        rvar = "r" ++ show (i+2)  
        f = ET.Var fvar
        x = ET.Var xvar 
        r = ET.Var rvar 
        (j1, encfn) = compClient (i + 3) fn
        (j, encarg) = compClient j1 arg 
    in  (j, ET.Let fvar encfn
             (ET.Let xvar encarg
               (ET.Let rvar (ET.App f [x]) r))) 
compClient i (TT.App (TT.LocType Server) fn arg) = 
    let fvar = "f" ++ show i 
        xvar = "x" ++ show (i+1) 
        rvar = "r" ++ show (i+2)  
        f = ET.Var fvar
        x = ET.Var xvar 
        r = ET.Var rvar
        (j1, encfn) = compClient (i + 3) fn
        (j2, encarg) = compClient j1 arg 

        contxvar = "x" ++ show j2 
        contx = ET.Var contxvar 
        idcont = ET.Lam Server [contxvar] contx 

        j = j2 + 1
    in  (j, ET.Let fvar encfn
             (ET.Let xvar encarg
               (ET.Let rvar (ET.Req f [x, idcont]) r)))
compClient i tt = error ("compClient: " ++ TT.prTyTerm tt)

type EncContTerm = EncTerm  -- continuation

-- Compilation for Server
compServer :: Int -> TypedTerm -> EncContTerm -> (Int, EncTerm)
compServer i (TT.Const c) k = 
    let rvar = "r" ++ show i 
        r = ET.Var rvar 
        j = i + 1
    in  (j, ET.Let rvar (ET.App k [ET.Const c]) r)
compServer i (TT.Var x) k = 
    let rvar = "r" ++ show i 
        r = ET.Var rvar 
        j = i + 1
    in  (j, ET.Let rvar (ET.App k [ET.Var x]) r)
compServer i (TT.Lam Client x ty m) k = 
    let rvar = "r" ++ show i 
        r = ET.Var rvar 

        (j, encm) = compClient (i + 1) m 
    in  (j, ET.Let rvar (ET.App k [ET.Lam Client [x] encm]) r)
compServer i (TT.Lam Server x ty m) k = 
    let rvar = "r" ++ show i 
        contkvar = "k" ++ show (i + 1) 
        r = ET.Var rvar
        contk = ET.Var contkvar 

        (j, encm) = compServer (i + 3) m contk 
    in  (j, ET.Let rvar (ET.App k [ET.Lam Server [x,contkvar] encm]) r)
compServer i (TT.App (TT.LocType Client) fn arg) k = 
    let fvar = "f" ++ show i
        xvar = "x" ++ show (i + 1) 
        zvar = "z" ++ show (i + 2) 
        rvar = "r" ++ show (i + 3)  

        f = ET.Var fvar 
        x = ET.Var xvar 
        z = ET.Var zvar 
        r = ET.Var rvar

        commuteFun = ET.Lam Client [zvar]
                        (ET.Let rvar (ET.App f [z]) 
                          (ET.Req k [r]))
        argcont = ET.Lam Server [xvar] (ET.Call commuteFun [x])

        (j, encarg) = compServer (i + 4) arg argcont
        
        fncont = ET.Lam Server [fvar] encarg

    in  compServer j fn fncont
compServer i (TT.App (TT.LocType Server) fn arg) k = 
    let fvar = "f" ++ show i
        xvar = "x" ++ show (i + 1) 
        rvar = "r" ++ show (i + 2)  

        f = ET.Var fvar 
        x = ET.Var xvar 
        r = ET.Var rvar

        argcont = ET.Lam Server [xvar] 
                    (ET.Let rvar (ET.App f [x,k]) r)
        (j, encarg) = compServer (i + 3) arg argcont 

        fncont = ET.Lam Server [fvar] encarg 
    in  compServer j fn fncont 
compServer i tt k =
    error ("compServer: " ++ TT.prTyTerm tt)