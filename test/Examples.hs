{-# LANGUAGE CPP #-}
module Main where

import Data.Functor
import Data.Monoid  hiding (Sum)
import System.Exit

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

mustProve :: String -> Term -> Tactic Derivation Goal -> Either String Term
mustProve msg a b =
    case prove a b of
        Proved _ e -> Right e
        Incomplete e -> Left (msg <> ": got incomplete! Remaining goals:\n" <> unlines (fmap show e))
        Failed e -> Left (msg <> ": got failed: " <> e)

mustFail :: String -> Term -> Tactic Derivation Goal -> Either String Term
mustFail msg a b =
    case prove a b of
        Failed _ -> Right a
        Incomplete _ -> Left (msg <> ": got incomplete!")
        Proved _ _ -> Left (msg <> ": got proved!")

testProof :: (String -> Term -> Tactic Derivation Goal -> Either String Term)
          -> String -> Term -> Tactic Derivation Goal -> IO Bool
testProof test name t tac = do
    putStrLn ("\nCASE: " <> name)
    print t
    putStrLn (pretty t)
    case test name t tac of
        Right e -> putStrLn ("OK: " <> (pretty e) <> "\n") >> return True
        Left  e -> putStrLn ("FAILED: " <> e <> "\n") >> return False

testProve = testProof mustProve
testFail = testProof mustFail

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

theorems :: [(String, Term, PrlTactic)]
theorems =
  [
    -- Base tests

    ( "Base.Eq"
    , (Eq Base Base (Uni 0))
    , baseEQ
    )

  , ( "Base.Eq"
    , (Eq Base Base (Uni 1))
    , baseEQ
    )

  , ( "Base.MemEq"
    , (Eq TT TT Base)
    , (baseMEMEQ `next` ceqREFL)
    )

  , ( "Base.MemEq"
    , (Eq (Ap (Lam (Var 0)) TT) TT Base)
    , (baseMEMEQ `next` ceqSTEP `next` ceqREFL)
    )

  , ( "Base.ElimEq"
    ,  (Pi (Eq TT Unit Base) (CEq TT Unit))
    , (piINTRO 0 `splitTac`
       [ eqEQ `splitTac` [baseEQ, baseMEMEQ `next` ceqREFL, baseMEMEQ `next` ceqREFL]
       , baseELIMEQ 0 `next` generalHYP 0
       ])
    )


    -- Ceq tests

  , ( "Ceq.Refl"
    , (CEq (Var 0) (Var 0))
    , ceqREFL
    )

  , ( "Ceq.Refl"
    , (CEq TT TT)
    , ceqREFL
    )

  , ( "Ceq.Refl"
    , (CEq
        (Pi (Pi (Var 0) (Var 1)) Unit)
        (Pi (Pi (Var 0) (Var 1)) Unit))
    , ceqREFL
    )

  , ( "Ceq.MemEq"
    , (Eq TT TT (CEq Unit Unit))
    , (ceqMEMEQ `next` ceqREFL)
    )

  , ( "Ceq.MemEq"
    , (Eq TT TT (CEq (Ap (Lam (Var 0)) Unit) Unit))
    , (ceqMEMEQ `next` ceqSTEP `next` ceqREFL)
    )

  , ( "Ceq.Sym"
    , (CEq Unit (Ap (Lam (Var 0)) Unit))
    , (ceqSYM `next` ceqSTEP `next` ceqREFL)
    )

  , ( "Ceq.Sym"
    , (CEq (Ap (Lam (Var 0)) Unit) Unit)
    , (ceqSYM `next` ceqSYM `next` ceqSTEP `next` ceqREFL)
    )

  , ( "Ceq.Step"
    , (CEq
       (NatRec (Succ (Succ (Succ Zero))) (Succ (Succ Zero)) (Succ (Var 1)))
       (Succ (Succ (Succ (Succ (Succ Zero))))))
    , (repeatTac (ceqSTEP `next` ceqREFL))
    )

  , ( "Ceq.Subst"
    , (Pi (CEq Zero (Succ Zero)) (CEq (NatRec Zero TT Unit) Unit))
    , (piINTRO 0 `splitTac`
       [ ceqEQ `splitTac` [ceqREFL, ceqREFL]
       , ceqSUBST (CEq Zero (Succ Zero))
         (CEq (NatRec (Var 0) TT Unit) Unit)
         `splitTac` [generalHYP 0, ceqSTEP `next` ceqREFL]
       ])
    )

  -- Eq tests

  , ( "Eq.Eq"
    , (Eq (Eq Unit Unit (Uni 0)) (Eq Unit Unit (Uni 0)) (Uni 1))
    , (eqEQ `splitTac` [uniEQ, unitEQ, unitEQ])
    )

  , ( "Eq.Eq"
    , (Eq (Eq Unit Base (Uni 0)) (Eq Unit Base (Uni 0)) (Uni 1))
    , (eqEQ `splitTac` [uniEQ, unitEQ, baseEQ])
    )

  , ( "Eq.MemEq"
    , (Eq TT TT (Eq Unit Unit (Uni 0)))
    , (eqMEMEQ `next` unitEQ)
    )

  , ( "Eq.EqSym"
    , (Eq TT TT (Eq Unit Unit (Uni 0)))
    , (eqSYM `next` eqMEMEQ `next` unitEQ)
    )

  , ( "Eq.Subst"
    , (Pi
       (Eq Zero (Succ Zero) Nat)
       (CEq (NatRec Zero Base Unit) Unit))
    , (piINTRO 0 `splitTac`
       [ eqEQ `splitTac` [natEQ, natZEROEQ, natSUCCEQ `next` natZEROEQ]
       , (eqSUBST 0 (Eq Zero (Succ Zero) Nat)
          (CEq (NatRec (Var 0) Base Unit) Unit)) `splitTac`
         [ ceqEQ `splitTac` [ceqREFL, ceqREFL]
         , generalHYP 0
         , ceqSTEP `next` ceqREFL]])
    )

    -- Sigma

  , ( "Sigma.Eq"
    , (Eq (Sigma Nat Base) (Sigma Nat Base) (Uni 0))
    , (sigmaEQ `splitTac` [natEQ, baseEQ])
    )

  ]

nontheorems :: [(String, Term, PrlTactic)]
nontheorems =
  [
    ( "Ceq.Refl"
    , (CEq TT Unit)
    , ceqREFL
    )
  ]

testCase :: Term -> IO ()
testCase t = do
  putStrLn "\nCASE"
  print t
  putStrLn $ pretty t
  print (pretty <$> deepStep t)
  putStrLn ""

main :: IO ()
main = do
  mapM_ testCase cases

  ps <- mapM (\(n,t,p) -> testProve n t p) theorems
  rs <- mapM (\(n,t,p) -> testFail n t p) nontheorems

  if (and ps && and rs)
    then exitSuccess
    else exitFailure

  putStrLn "Done!"
