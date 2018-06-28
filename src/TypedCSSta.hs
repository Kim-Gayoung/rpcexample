module TypedCSSta where

import Term(Location(..))
import TypedTerm as TT 
import CSStaTerm as ST 
import Data.List

--
data Context = Ctx String StaTerm
type ClientContext = Context 
type ServerContext = [Context]   -- a stack of contexts

type EitherSta = Either (StaTerm, ServerContext) (ClientContext, ServerContext, StaTerm)

lookup :: FunStore -> String -> ClosedFun
lookup fs f =
    case Data.List.lookup f fs of
        Just closedFun -> closedFun
        Nothing -> error ("lookup: not found " ++ f ++ "\n")

--
eval :: FunStore -> FunStore -> StaTerm -> StaValue 
eval fs_c fs_s m = repEvalClient fs_c fs_s m []

repEvalClient :: FunStore -> FunStore -> StaTerm -> ServerContext -> StaTerm 
repEvalClient fs_c fs_s m serverContext =
    case evalClient fs_c m serverContext of
        Left (v@(ST.Clo _ _), []) -> v
        Left (v@(ST.Const _), []) -> v
        Left (m', serverContext) -> repEvalClient fs_c fs_s m' serverContext
        Right (clientCtx', serverCtx', m') -> repEvalServer fs_c fs_s clientCtx' serverCtx' m'

repEvalServer :: FunStore -> FunStore -> ClientContext -> ServerContext -> StaTerm -> StaTerm 
repEvalServer fs_c fs_s clientCtx serverCtx m = 
    case evalServer fs_s clientCtx serverCtx m of
        Left (m', serverCtx') -> repEvalClient fs_c fs_s m' serverCtx'
        Right (clientCtx', serverCtx', m') -> repEvalServer fs_c fs_s clientCtx' serverCtx' m'

--
evalClient :: FunStore -> StaTerm -> ServerContext -> EitherSta
evalClient phi (ST.Let y (ST.App v@(ST.Clo f vs) ws) m) serverCtx =
    let (zs, a, xs, m0) = TypedCSSta.lookup phi f
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
evalServer phi clientCtx serverCtx (ST.Let y (ST.App v@(ST.Clo f vs) ws) m) = 
    let (zs, a, xs, m0) = TypedCSSta.lookup phi f
    in Right (clientCtx, serverCtx, ST.Let y (substs (substs m0 zs vs) xs ws) m)
evalServer phi (Ctx y m2) serverCtx (ST.Let x (ST.Call v@(ST.Clo f vs) ws) m1) =
    Left (ST.Let y (ST.App v ws) m2, Ctx x m1 : serverCtx)
evalServer phi (Ctx x m) serverCtx v@(ST.Clo _ _) = 
    Left (ST.Let x v m, serverCtx)
evalServer phi (Ctx x m) serverCtx v@(ST.Const _) = 
    Left (ST.Let x v m, serverCtx)
evalServer phi clientCtx serverCtx (ST.Let x v@(ST.Clo _ _) m) =
    Right (clientCtx, serverCtx, ST.subst m x v)
evalServer phi clientCtx serverCtx (ST.Let x v@(ST.Const _) m) =
    Right (clientCtx, serverCtx, ST.subst m x v)
evalServer phi clientCtx serverCtx (ST.Let x (ST.Let y m1 m2) m) = 
    Right (clientCtx, serverCtx, ST.Let y m1 (ST.Let x m2 m))
evalServer phi clientCtx serverCtx m =
    error ("evalServer: " ++ prTerm m)
