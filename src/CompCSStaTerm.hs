module CompCSStaTerm where

import Term(Location(..))
import RPCStaTerm as RT
import CSStaTerm as CT

-- Compilation for Client
compCSStaTerm :: RT.StaTerm -> (CT.StaTerm, FunStore, FunStore)
compCSStaTerm tt = let (_, m, fs_c, fs_s) = (comp 1 tt [])
                   in (m, fs_c, fs_s)

comp :: Int -> RT.StaTerm -> [String] -> (Int, CT.StaTerm, FunStore, FunStore) 
comp i (RT.Const c) zs = (i, CT.Const c, [], [])
comp i (RT.Var x) zs = (i, CT.Var x, [], []) 
comp i (RT.Lam loc xs m) zs =
    let (j, m', fs_c, fs_s) = comp i m (zs ++ xs)
        closedFun = (fvs, loc, xs, m')
        f = "_gf" ++ show j
        fs_c' = if loc == Client then fs_c ++ [(f, closedFun)] else fs_c
        fs_s' = if loc == Server then fs_s ++ [(f, closedFun)] else fs_s
        fvs = fv (RT.Lam loc xs m)
    in  (j+1, CT.Clo f (map CT.Var fvs), fs_c', fs_s')
comp i (RT.App fn args) zs = 
    let (j1, csfn, fs_c, fs_s) = comp i fn zs
        (j2, csargs, fs_cs, fs_ss) = compList j1 args zs
    in (j2, CT.App csfn csargs, fs_c ++ fs_cs, fs_s ++ fs_ss)
comp i (RT.Let y m1 m2) zs = 
    let (j1, m1', fs_c1, fs_s1) = comp i m1 zs
        (j2, m2', fs_c2, fs_s2) = comp j1 m2 (zs ++ [y])
        fs_c' = fs_c1 ++ fs_c2
        fs_s' = fs_s1 ++ fs_s2
    in (j2, CT.Let y m1' m2', fs_c', fs_s')
comp i (RT.Req v ws) zs = 
    let (j1, v', fs_c, fs_s) = comp i v zs
        (j', ws', fs_cs, fs_ss) = compList j1 ws zs
    in (j', CT.Req v' ws', fs_c ++ fs_cs, fs_s ++ fs_ss)
comp i (RT.Call v ws) zs = 
    let (j1, v', fs_c, fs_s) = comp i v zs
        (j', ws', fs_cs, fs_ss) = compList j1 ws zs
    in (j', CT.Call v' ws', fs_c ++ fs_cs, fs_s ++ fs_ss)
comp i (RT.Ret v) zs = 
    let (j, v', fs_c, fs_s) = comp i v zs
    in (j, CT.Ret v', fs_c, fs_s)
comp i tt zs = error ("comp: " ++ RT.prTerm tt)

compList :: Int -> [RT.StaTerm] -> [String] -> (Int, [CT.StaTerm], FunStore, FunStore) 
compList i [] zs = (i, [], [], [])
compList i (m:ms) zs =
    let (j', ms', fs_cs', fs_ss') = compList i ms zs
        (j, m', fs_c', fs_s') = comp j' m zs
    in (j, m':ms', fs_c' ++ fs_cs', fs_s' ++ fs_ss')
