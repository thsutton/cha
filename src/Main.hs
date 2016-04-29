{-# LANGUAGE CPP #-}
module Main where

import Data.Functor
import Data.Monoid  hiding (Sum)

import Derivation
import Extract
import Goal
import Interp
import Refiner
import Rules
import Tactic
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

mustProve :: String -> Term -> Tactic Derivation Goal -> Either String Term
mustProve msg a b =
    case prove a b of
        Proved _ e -> Right e
        Incomplete _ -> Left (msg <> ": got imcomplete!")
        Failed -> Left (msg <> ": got failed!")

mustFail :: String -> Term -> Tactic Derivation Goal -> Either String Term
mustFail msg a b =
    case prove a b of
        Failed -> Right a
        Incomplete _ -> Left (msg <> ": got incomplete!")
        Proved _ _ -> Left (msg <> ": got proved!")

testCase :: Term -> IO ()
testCase t = do
  putStrLn "\nCASE"
  print t
  putStrLn $ pretty t
  print (pretty <$> deepStep t)
  putStrLn ""

testProof :: (String -> Term -> Tactic Derivation Goal -> Either String Term)
          -> String -> Term -> Tactic Derivation Goal -> IO ()
testProof test name t tac = do
    putStrLn ("\nCASE: " <> name)
    print t
    putStrLn (pretty t)
    case test name t tac of
        Right e -> putStrLn ("OK: " <> (pretty e))
        Left  e -> putStrLn ("FAILED: " <> e)
    putStrLn ""

testProve = testProof mustProve
testFail = testProof mustFail

main :: IO ()
main = do
  mapM_ testCase cases

  testProve "Base.Eq" (Eq Base Base (Uni 0)) eq
  testProve "Base.Eq" (Eq Base Base (Uni 1)) eq
  testProve "Base.MemEq" (Eq TT TT Base) (memEq `next` ceqRefl)
  testProve "Base.MemEq"
    (Eq (Ap (Lam (Var 0)) TT) TT Base)
    (memEq `next` ceqStep `next` ceqRefl)

  {-
  testProve "Base.ElimEq"
    (Pi (Eq TT Unit Base) (Ceq TT Unit))
    (Pi.Intro 0 `splitTac`
     [ Eq.Eq `splitTac` [Base.Eq, Base.MemEq `next` Ceq.Refl, Base.MemEq `next` Ceq.Refl]
     , Base.ElimEq 0 `next` General.Hyp 0
    ])
  -}
  putStrLn "Done!"
