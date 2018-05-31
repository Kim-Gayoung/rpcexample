module TypedRPCEnc where

import Term(Location(..))
import TypedTerm as TT 
import EncTerm as ET 

--
eval :: EncTerm -> EncValue 
eval m = repEvalClient m 

repEvalClient :: EncTerm -> EncTerm 
repEvalClient m =
    case evalClient m of
        Left m' -> repEvalClient m'
        Right (ctx, m') -> repEvalServer ctx m'

repEvalServer :: ClientContext -> EncTerm -> EncTerm 
repEvalServer ctx m = 
    case evalServer ctx m of
        Left m' -> repEvalClient m'
        Right (ctx', m') -> repEvalServer ctx' m'

evalClient :: EncTerm -> Either EncTerm (ClientContext, EncTerm)
evalClient (ET.LetApp y v@(ET.Lam Client xs m0) ws m) =
    Left (ET.Let y (ET.substs m0 xs ws) m)
evalClient (ET.LetReq y v@(ET.Lam Client xs m0) ws m) =
    Right (Ctx y m, ET.LetApp "r" v ws (ET.Var "r"))
evalClient (ET.Let y v@(ET.Lam _ _ _) m) = Left (ET.subst m y v)
evalClient (ET.Let x (ET.Let y m1 m2) m) = 
    Left (ET.Let y m1 (ET.Let x m2 m))

data Context = Ctx String EncTerm
type ClientContext = Context 

evalServer :: ClientContext -> EncTerm -> Either EncTerm (ClientContext, EncTerm) 
evalServer clientCtx (ET.LetApp y v@(ET.Lam Server xs m0) ws m) =
    Right (clientCtx, ET.Let y (ET.substs m0 xs ws) m) 
evalServer clientCtx@(Ctx x m) (ET.Call v ws) = 
    Left (ET.LetApp x v ws m) 
evalServer clientCtx@(Ctx x m) v@(ET.Lam _ _ _) = 
    Left (ET.Let x v m)
evalServer clientCtx (ET.Let x v@(ET.Lam _ _ _) m) = 
    Right (clientCtx, ET.subst m x v) 
evalServer clientCtx (ET.Let x (ET.Let y m1 m2) m) =
    Right (clientCtx, ET.Let y m1 (ET.Let x m2 m))


