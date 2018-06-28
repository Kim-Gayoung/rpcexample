-- Main
-- Run GHCi by stack ghci
--
-- *Main> 
-- [ 1 of 10] Compiling Lib              ( C:\Work\haskell\rpc\src\Lib.hs, interpreted )
-- [ 2 of 10] Compiling Term             ( C:\Work\haskell\rpc\src\Term.hs, interpreted )
-- [ 3 of 10] Compiling RPC              ( C:\Work\haskell\rpc\src\RPC.hs, interpreted )
-- [ 4 of 10] Compiling EncTerm          ( C:\Work\haskell\rpc\src\EncTerm.hs, interpreted )
-- [ 5 of 10] Compiling TypedTerm        ( C:\Work\haskell\rpc\src\TypedTerm.hs, interpreted )
-- [ 6 of 10] Compiling TypedRPCEnc      ( C:\Work\haskell\rpc\src\TypedRPCEnc.hs, interpreted )
-- [ 7 of 10] Compiling Infer            ( C:\Work\haskell\rpc\src\Infer.hs, interpreted )
-- [ 8 of 10] Compiling TypedRPC         ( C:\Work\haskell\rpc\src\TypedRPC.hs, interpreted )
-- [ 9 of 10] Compiling CompEncTerm      ( C:\Work\haskell\rpc\src\CompEncTerm.hs, interpreted )
-- [10 of 10] Compiling Main             ( C:\Work\haskell\rpc\app\Main.hs, interpreted )
-- Ok, 10 modules loaded.
-- Loaded GHCi configuration from C:\Users\khchoi\AppData\Local\Temp\haskell-stack-ghci\4dd8f52a\ghci-script
--
-- Then run main
--
-- *Main> main
-- In RPC:
-- (lam^s f. (lam^s x. x) ((f) (1))) (lam^c y. (lam^s z. z) (y))
--  evaluates to
-- 1

-- In type inference:
-- (lam^s (f:(int-c->int)). (lam^s (x:int). x)^s^((f)^c^(1)))^s^(lam^c (y:int). (lam^s (z:int). z)^s^(y))

-- In State-encoding RPC:
-- let f1 = lam^s(f,k4).let r14 = (lam^s(f5).let r13 = (lam^s(f8).let r12 = (lam^s(x9).Call(lam^c(z10).let r11 = (f8) (z10) in Req(lam^s(x6).let r7 = (f5) (x6,k4) in r7) (r11)) (x9)) (1) in r12) (f) in r13) (lam^s(x,k15).let r17 = (k15) (x) in r17) in r14 in let x2 = lam^c(y).let f18 = lam^s(z,k21).let r22 = (k21) (z) in r22 in let x19 = y in let r20 = Req(f18) (x19,lam^s(x23).x23) in r20 in let r3 = Req(f1) (x2,lam^s(x24).x24) in r3

--  evaluates to
-- 1

-- In Stateful RPC:
-- let f1 = lam^s(f).let f4 = lam^s(x).x in let x5 = let f7 = f in let x8 = 1 in let r11 = Call(lam^c(z10).let y9 = (f7) (z10) in Ret(y9)) (x8) in r11 in let r6 = (f4) (x5) in r6 in let x2 = lam^c(y).let f12 = lam^s(z).z in let x13 = y in let r14 = Req(f12) (x13) in r14 in let r3 = Req(f1) (x2) in r3

--  evaluates to
-- 1

module Main where

import Term
import RPC

import TypedTerm(prTyTerm)
import TypedRPC

import RPCEncTerm(prTerm)
import TypedRPCEnc
import CompRPCEncTerm

import RPCStaTerm(prTerm)
import TypedRPCSta
import CompRPCStaTerm

import CSStaTerm(prTerm)
import TypedCSSta
import CompCSStaTerm

main :: IO ()
main = do 
    putStrLn "In RPC: "
    putStrLn (Term.prTerm ex1) 
    putStrLn " evaluates to " 
    putStrLn $ Term.prTerm $ RPC.eval ex1 Client
    putStrLn ""

    putStrLn "In type inference: "
    let tyex1 = elaborate ex1
    putStrLn (prTyTerm tyex1)
    putStrLn ""

    putStrLn "In State-encoding RPC: "
    let encex1 = compRPCEncTerm tyex1
    putStrLn (RPCEncTerm.prTerm encex1)
    putStrLn ""

    putStrLn " evaluates to "
    let encv = TypedRPCEnc.eval encex1 
    putStrLn (RPCEncTerm.prTerm encv)
    putStrLn ""

    putStrLn "In Stateful RPC: "
    let staex1 = compRPCStaTerm tyex1
    putStrLn (RPCStaTerm.prTerm staex1)
    putStrLn ""

    putStrLn " evaluates to "
    let stav = TypedRPCSta.eval staex1 
    putStrLn (RPCStaTerm.prTerm stav)

    putStrLn "In Stateful CS: "
    let (csstaex1, fs_c, fs_s) = compCSStaTerm staex1
    putStrLn (CSStaTerm.prTerm csstaex1)
    putStrLn ""

    putStrLn " evaluates to "
    let csstav = TypedCSSta.eval fs_c fs_s csstaex1 
    putStrLn (CSStaTerm.prTerm csstav)

--
ex1Left = Lam Server "f" 
        (App (Lam Server "x" (Var "x")) 
            (App (Var "f") (Const 1)))
ex1Right = Lam Client "y"
        (App (Lam Server "z" (Var "z")) (Var "y"))

ex1 = App ex1Left ex1Right