-- |
--
-- These definitions are based on those found in @rules/utils.sml@.

module Rules.Utils where

import Derivation
import Goal
import Tactic
import Term

-- | Tactics which operate on our 'Term's and 'Derivation's.
type PrlTactic = Tactic Derivation Goal

type Target = Int

type Universe = Int

-- | Add a 'Term' to the head of a context.
--
-- The term will be marked as computationally relevant.
(<:>) :: Term -> Context -> Context
t <:> ctx = (Visible, t) : ctx

-- | Is a 'Term' proof relevant or not?
irrelevant :: Term -> Bool
irrelevant t =
    case t of
        Eq a b t -> True
        CEq a b -> True
        Var i -> False
        Lam b -> False
        Ap f a -> False
        Pi a b -> False
        Pair l r -> False
        Fst e -> False
        Snd e -> False
        Sigma a b -> False
        Zero -> False
        Succ t -> False
        NatRec n z s -> False
        Nat -> False
        TT -> False
        Unit -> True
        Base -> False
        Uni i -> False
        Per per -> False
        Fix e -> False
#ifdef FLAG_coind
        -- TODO co/inductive cases.
#endif

