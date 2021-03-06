module TypedRPCSta where


import Term(Location(..))
import TypedTerm as TT 
import RPCStaTerm as ST 

--
data Context = Ctx String StaTerm
type ClientContext = Context 
type ServerContext = [Context]   -- a stack of contexts

type EitherSta = Either (StaTerm, ServerContext) (ClientContext, ServerContext, StaTerm)

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
evalClient :: StaTerm -> ServerContext -> EitherSta
evalClient (ST.Let y (ST.App v@(ST.Lam Client xs body) ws) m) serverCtx = 
    Left (ST.Let y (substs body xs ws) m, serverCtx)
evalClient (ST.Let x (ST.Req v@(ST.Lam Server _ _) ws) m) serverCtx =
    let rvar = "r"
        r = ST.Var rvar 
    in Right (Ctx x m, serverCtx, ST.Let rvar (ST.App v ws) r)
evalClient (ST.Let x v@(ST.Lam _ _ _) m) serverCtx = Left (ST.subst m x v, serverCtx)
evalClient (ST.Let x v@(ST.Const _) m) serverCtx = Left (ST.subst m x v, serverCtx)
evalClient (ST.Let x (ST.Let y m1 m2) m) serverCtx = 
    Left (ST.Let y m1 (ST.Let x m2 m), serverCtx) 
evalClient (ST.Let y (ST.Ret v) m2) (Ctx x m1 : serverCtx) = 
    Right (Ctx y m2, serverCtx, ST.Let x v m1)
evalClient m serverCtx =
    error ("evalClient: " ++ prTerm m)

evalServer :: ClientContext -> ServerContext -> StaTerm -> EitherSta 
evalServer clientCtx serverCtx (ST.Let y (ST.App v@(ST.Lam Server xs body) ws) m) = 
    Right (clientCtx, serverCtx, ST.Let y (substs body xs ws) m)
evalServer (Ctx y m2) serverCtx (ST.Let x (ST.Call v@(ST.Lam Client xs body) ws) m1) =
    Left (ST.Let y (ST.App v ws) m2, Ctx x m1 : serverCtx)
evalServer (Ctx x m) serverCtx v@(ST.Lam _ _ _) = 
    Left (ST.Let x v m, serverCtx)
evalServer (Ctx x m) serverCtx v@(ST.Const _) = 
    Left (ST.Let x v m, serverCtx)
evalServer clientCtx serverCtx (ST.Let x v@(ST.Lam _ _ _) m) =
    Right (clientCtx, serverCtx, ST.subst m x v)
evalServer clientCtx serverCtx (ST.Let x v@(ST.Const _) m) =
    Right (clientCtx, serverCtx, ST.subst m x v)
evalServer clientCtx serverCtx (ST.Let x (ST.Let y m1 m2) m) = 
    Right (clientCtx, serverCtx, ST.Let y m1 (ST.Let x m2 m))
evalServer clientCtx serverCtx m =
    error ("evalServer: " ++ prTerm m)
