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

numeral :: Int -> Term
numeral n
    | n == 0    = Fold nat (InR Unit)
    | n  < 0    = error "No numerals less than zero"
    | otherwise = Fold nat (InL (numeral $ n - 1))
#endif

cases :: [Term]
cases = [ Fst (Pair Unit TT)
        , Snd (Pair Unit TT)
        , let p = Pair Unit TT in Pair (Snd p) (Fst p)
#ifdef FLAG_coind
        , Case (InR Unit) (Void) (Lam (Pair (Var 0) (Var 1)))
        , Rec nat (Var 0) (Fold nat (InL Unit))
        , Map nat TT t_e
        , Rec nat (Case (Var 0) (Zero) (Succ (Var 0))) (numeral 0)
        , Rec nat (Case (Var 0) (Zero) (Succ (Var 0))) (numeral 2)
        , r
#endif
        ]

testCase :: Term -> IO ()
testCase t = do
  putStrLn "\nCASE"
  print t
  putStrLn $ pretty t
  print (pretty <$> deepStep t)
  putStrLn ""

main :: IO ()
main = mapM_ testCase cases
