module TypedCSEnc where

import Term(Location(..))
import TypedTerm as TT
import CSEncTerm as ET
import Data.List

--
data Context = Ctx String EncTerm
type ClientContext = Context

lookup :: FunStore -> String -> ClosedFun
lookup fs f =
    case Data.List.lookup f fs of
        Just closedFun -> closedFun
        Nothing -> error ("lookup: not found " ++ f ++ "\n")

--
eval :: FunStore -> FunStore -> EncTerm -> EncValue
eval fs_c fs_s m = repEvalClient fs_c fs_s m

repEvalClient :: FunStore -> FunStore -> EncTerm -> EncTerm
repEvalClient fs_c fs_s m = 
    case evalClient fs_c m of
        Left v@(ET.Clo _ _) -> v
        Left v@(ET.Const _) -> v
        Left m' -> repEvalClient fs_c fs_s m'
        Right (ctx, m') -> repEvalServer fs_c fs_s ctx m'

repEvalServer :: FunStore -> FunStore -> ClientContext -> EncTerm -> EncTerm 
repEvalServer fs_c fs_s ctx m = 
    case evalServer fs_s ctx m of
        Left m' -> repEvalClient fs_c fs_s m'
        Right (ctx', m') -> repEvalServer fs_c fs_s ctx' m'

evalClient :: FunStore -> EncTerm -> Either EncTerm (ClientContext, EncTerm)
evalClient phi (ET.Let y (ET.App (ET.Clo f vs) ws) m) =
    let (zs, a, xs, m0) = TypedCSEnc.lookup phi f
    in Left (ET.Let y (ET.substs (ET.substs m0 zs vs) xs ws) m)
evalClient phi (ET.Let y (ET.Req v@(ET.Clo _ _) ws) m) =
    Right (Ctx y m, ET.App v ws)
evalClient phi (ET.Let y v@(ET.Clo _ _ ) m) = Left (ET.subst m y v)
evalClient phi (ET.Let y v@(ET.Const _) m) = Left (ET.subst m y v)
evalClient phi (ET.Let x (ET.Let y m1 m2) m) = 
    Left (ET.Let y m1 (ET.Let x m2 m))
evalClient phi encm = error ("evalClient: " ++ prTerm encm)

evalServer :: FunStore -> ClientContext -> EncTerm -> Either EncTerm (ClientContext, EncTerm) 
evalServer phi clientCtx (ET.App (ET.Clo f vs) ws) =
    let (zs, a, xs, m0) = TypedCSEnc.lookup phi f
    in Right (clientCtx, ET.substs (ET.substs m0 zs vs) xs ws)
evalServer phi clientCtx@(Ctx x m) (ET.Call v@(ET.Clo _ _) ws) = 
    Left (ET.Let x (ET.App v ws) m)
evalServer phi clientCtx@(Ctx x m) v@(ET.Clo _ _) = 
    Left (ET.Let x v m)
evalServer phi clientCtx@(Ctx x m) v@(ET.Const _) = 
    Left (ET.Let x v m)
evalServer phi clientCtx encm = error ("evalServer: " ++ prTerm encm)