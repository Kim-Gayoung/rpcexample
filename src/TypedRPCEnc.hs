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
evalClient (ET.Let y (ET.App (ET.Lam Client xs m0) ws) m) =
    Left (ET.Let y (ET.substs m0 xs ws) m)
evalClient (ET.Let y (ET.Req v@(ET.Lam Client xs m0) ws) m) =
    Right (Ctx y m, ET.Let "r" (ET.App v ws) (ET.Var "r"))
evalClient (ET.Let y v@(ET.Lam _ _ _) m) = Left (ET.subst m y v)
evalClient (ET.Let x (ET.Let y m1 m2) m) = 
    Left (ET.Let y m1 (ET.Let x m2 m))

data Context = Ctx String EncTerm
type ClientContext = Context 

evalServer :: ClientContext -> EncTerm -> Either EncTerm (ClientContext, EncTerm) 
evalServer clientCtx (ET.Let y (ET.App (ET.Lam Server xs m0) ws) m) =
    Right (clientCtx, ET.Let y (ET.substs m0 xs ws) m) 
evalServer clientCtx@(Ctx x m) (ET.Call v ws) = 
    Left (ET.Let x (ET.App v ws) m)
evalServer clientCtx@(Ctx x m) v@(ET.Lam _ _ _) = 
    Left (ET.Let x v m)
evalServer clientCtx (ET.Let x v@(ET.Lam _ _ _) m) = 
    Right (clientCtx, ET.subst m x v) 
evalServer clientCtx (ET.Let x (ET.Let y m1 m2) m) =
    Right (clientCtx, ET.Let y m1 (ET.Let x m2 m))


