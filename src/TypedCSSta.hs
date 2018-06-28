module TypedCSSta where

import Term(Location(..))
import TypedTerm as TT 
import CSStaTerm as ST 

--
data Context = Ctx String StaTerm
type ClientContext = Context 
type ServerContext = [Context]   -- a stack of contexts

type EitherSta = Either (StaTerm, ServerContext) (ClientContext, ServerContext, StaTerm)

lookup :: FunStore -> String -> ClosedFun
lookup fs f =
    case Data.List.lookup fs f of
        Just closedFun -> closedFun
        Nothing -> error ("lookup: not found " ++ f ++ "\n" ++ show fs)

--
eval :: StaTerm -> StaValue 
eval m = repEvalClient m []

repEvalClient :: StaTerm -> ServerContext -> StaTerm 
repEvalClient m serverContext =
    case evalClient m serverContext of
        Left (v@(ST.Lam _ _ _), []) -> v
        Left (v@(ST.Const _), []) -> v
        Left (m', serverContext) -> repEvalClient m' serverContext
        Right (clientCtx', serverCtx', m') -> repEvalServer clientCtx' serverCtx' m'

repEvalServer :: ClientContext -> ServerContext -> StaTerm -> StaTerm 
repEvalServer clientCtx serverCtx m = 
    case evalServer clientCtx serverCtx m of
        Left (m', serverCtx') -> repEvalClient m' serverCtx'
        Right (clientCtx', serverCtx', m') -> repEvalServer clientCtx' serverCtx' m'

--
evalClient :: FunStore -> StaTerm -> ServerContext -> EitherSta
evalClient phi (ST.Let y (ST.App v@(ST.Clo f vs) ws) m) serverCtx =
    let (zs, a, xs, m0) = lookup phi f
    in Left (ST.Let y (substs (substs m0 zs vs) xs ws) m, serverCtx)
                        -- substs m0 (zs ++ xs) (vs ++ ws)
evalClient phi (ST.Let x (ST.Req v@(ST.Clo f vs) ws) m) serverCtx =
    let rvar = "r"
        r = ST.Var rvar 
    in Right (Ctx x m, serverCtx, ST.Let rvar (ST.App v ws) r)
evalClient phi (ST.Let x v@(ST.Clo _ _) m) serverCtx = Left (ST.subst m x v, serverCtx)
evalClient phi (ST.Let x v@(ST.Const _) m) serverCtx = Left (ST.subst m x v, serverCtx)
evalClient phi (ST.Let x (ST.Let y m1 m2) m) serverCtx = 
    Left (ST.Let y m1 (ST.Let x m2 m), serverCtx) 
evalClient phi (ST.Let y (ST.Ret v) m2) (Ctx x m1 : serverCtx) = 
    Right (Ctx y m2, serverCtx, ST.Let x v m1)
evalClient phi m serverCtx =
    error ("evalClient: " ++ prTerm m)

evalServer :: FunStore -> ClientContext -> ServerContext -> StaTerm -> EitherSta 
evalServer phi clientCtx serverCtx (ST.Let y (ST.App v@(ST.Lam Server xs body) ws) m) = 
    Right (clientCtx, serverCtx, ST.Let y (substs body xs ws) m)
evalServer phi (Ctx y m2) serverCtx (ST.Let x (ST.Call v@(ST.Lam Client xs body) ws) m1) =
    Left (ST.Let y (ST.App v ws) m2, Ctx x m1 : serverCtx)
evalServer phi (Ctx x m) serverCtx v@(ST.Clo _ _) = 
    Left (ST.Let x v m, serverCtx)
evalServer phi (Ctx x m) serverCtx v@(ST.Const _) = 
    Left (ST.Let x v m, serverCtx)
evalServer phi clientCtx serverCtx (ST.Let x v@(ST.Lam _ _ _) m) =
    Right (clientCtx, serverCtx, ST.subst m x v)
evalServer phi clientCtx serverCtx (ST.Let x v@(ST.Const _) m) =
    Right (clientCtx, serverCtx, ST.subst m x v)
evalServer phi clientCtx serverCtx (ST.Let x (ST.Let y m1 m2) m) = 
    Right (clientCtx, serverCtx, ST.Let y m1 (ST.Let x m2 m))
evalServer phi clientCtx serverCtx m =
    error ("evalServer: " ++ prTerm m)
