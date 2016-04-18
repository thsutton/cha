{-# LANGUAGE CPP #-}
module Main where

import Data.Functor
import Interp
import Term

#ifdef FLAG_coind
nat = Sum Unit (Var 0)
ten = Fold nat (last . take 3 $ (iterate InR (InL Unit)))

r = Rec nat (Case (Var 0) Zero (Succ (Var 0))) ten

t_ty = (Sum Unit (Sum (Var 0) Unit))
t_r = Case (Var 0) (Unit) (Void)
t_e = InR (InL Unit)
t_p = Map t_ty t_r t_e

id_e = (Var 0)

cases :: [Term]
cases = [ Case (InR Unit) (Void) (Lam (Pair (Var 0) (Var 1)))
        , Rec nat id_e (Fst $ Pair Unit TT)
        , Map nat TT t_e
        , r
        ]

a_case :: Term -> IO ()
a_case t = do
  putStrLn "\nCASE"
  putStrLn $ pretty t
  print $ (pretty <$> run t)
  putStrLn ""

main :: IO ()
main = do
  mapM_ a_case cases

#else

main :: IO ()
main = do
  putStrLn "hello world"

#endif

