module CompRPCStaTerm where

import Term(Location(..))
import TypedTerm as TT 
import RPCStaTerm as ST 

-- Compilation for Client
compRPCStaTerm :: TypedTerm -> StaTerm
compRPCStaTerm tt = snd (compClient 1 tt)

compClient :: Int -> TypedTerm -> (Int, StaTerm) 
compClient i (TT.Const c) = (i, ST.Const c)
compClient i (TT.Var x) = (i, ST.Var x) 
compClient i (TT.Lam Client x ty m) =
    let (j, m') = compClient i m 
    in  (j, ST.Lam Client [x] m') 
compClient i (TT.Lam Server x ty m) =
    let (j, m') = compServer i m 
    in  (j, ST.Lam Server [x] m')
compClient i (TT.App (TT.LocType Client) fn arg) = 
    let fvar = "f" ++ show i
        xvar = "x" ++ show (i+1)
        rvar = "r" ++ show (i+2)
        f = ST.Var fvar
        x = ST.Var xvar 
        r = ST.Var rvar
        (j1, stafn) = compClient (i+3) fn
        (j2, staarg) = compClient j1 arg
    in  (j2, ST.Let fvar stafn 
                (ST.Let xvar staarg
                    (ST.Let rvar (ST.App f [x]) r)))
compClient i (TT.App (TT.LocType Server) fn arg) =
    let fvar = "f" ++ show i
        xvar = "x" ++ show (i+1)
        rvar = "r" ++ show (i+2)
        f = ST.Var fvar 
        x = ST.Var xvar
        r = ST.Var rvar 
        (j1, stafn) = compClient (i+3) fn
        (j2, staarg) = compClient j1 arg
    in  (j2, ST.Let fvar stafn
                (ST.Let xvar staarg
                    (ST.Let rvar (ST.Req f [x]) r)))
compClient i tt = error ("compClient: " ++ TT.prTyTerm tt) 

-- Compilation for Server
compServer :: Int -> TypedTerm -> (Int, StaTerm)
compServer i (TT.Const c) = (i, ST.Const c)
compServer i (TT.Var x) = (i, ST.Var x)
compServer i (TT.Lam Client x ty m) = 
    let (j, m') = compClient i m 
    in  (j, ST.Lam Client [x] m') 
compServer i (TT.Lam Server x ty m) =
    let (j, m') = compServer i m 
    in  (j, ST.Lam Server [x] m')
compServer i (TT.App (TT.LocType Client) fn arg) = 
    let fvar = "f" ++ show i
        xvar = "x" ++ show (i + 1)
        yvar = "y" ++ show (i + 2)
        zvar = "z" ++ show (i + 3)
        rvar = "r" ++ show (i + 4)

        f = ST.Var fvar
        x = ST.Var xvar
        y = ST.Var yvar
        z = ST.Var zvar
        r = ST.Var rvar

        commuteFun = ST.Lam Client [zvar] 
                        (ST.Let yvar (ST.App f [z]) (ST.Ret y))
    
        (j1, stafn) = compServer (i+5) fn 
        (j2, staarg) = compServer j1 arg 
    in (j2, ST.Let fvar stafn 
                (ST.Let xvar staarg
                    (ST.Let rvar (ST.Call commuteFun [x]) r)))
compServer i (TT.App (TT.LocType Server) fn arg) = 
    let fvar = "f" ++ show i
        xvar = "x" ++ show (i + 1)
        rvar = "r" ++ show (i + 2)

        f = ST.Var fvar
        x = ST.Var xvar
        r = ST.Var rvar
    
        (j1, stafn) = compServer (i+3) fn
        (j2, staarg) = compServer j1 arg
    in  (j2, ST.Let fvar stafn
                (ST.Let xvar staarg
                    (ST.Let rvar (ST.App f [x]) r)))
compServer i tt = error ("compServer: " ++ TT.prTyTerm tt)