module Rules where

import Data.List   (nub)
import Data.Monoid

import Derivation
import Goal
import Interp
import Tactic
import Term

-- * Utilities

type PrlTactic = Tactic Derivation Goal

type Target = Int
type Universe = Int

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


-- * Base

-- |
--
--  H >> base = base in U(i)
eq :: PrlTactic
eq (Goal ctx t) =
    case t of
        Eq Base Base (Uni i) ->
            return $ Result
               { resultGoals = []
               , resultEvidence = \e -> case e of
                                          [] -> BASE_EQ
                                          _ -> error "EQ: Invalid evidence!"
               }
        _ -> fail "EQ failed"

-- |
--
-- H >> a = b in base
--   x in FV(a) => H(x) = base
--   x in FV(b) => H(x) = base
--   H >> a ~ b
memEq :: PrlTactic
memEq (Goal ctx t) =
    case t of
        Eq a b Base ->
            let vars = nub $ freevars a <> freevars b
            in if all (\v -> nth False v ctx == Just Base) vars
               then return $ Result
                        { resultGoals = [ Goal ctx (CEq a b) ]
                        , resultEvidence = \e -> case e of
                                                   [d] -> BASE_MEM_EQ d
                                                   _ -> error "MEMEQ: Invalid evidence!"
                        }
               else fail "MEMEQ failed"
        _ -> fail "MEMEQ does not apply."

-- |
-- H >> C
--   H(i) = (a = b in base)
-- H, a ~ b >> C
elimEq :: Target -> PrlTactic
elimEq target (Goal ctx t) =
    case nth (irrelevant t) target ctx of
        Just (Eq a b Base) ->
            -- We lift `t` because we've added to the head of `ctx`.
            return $ Result
                   { resultGoals = [Goal (CEq a b <:> ctx) (lift 0 1 t)]
                   , resultEvidence = \d ->
                                      case d of
                                        _ -> error "ELIMEQ: Invalid evidence!"

                   }
        _ -> fail "ELIMEQ does not apply."

-- * Ceq

ceqEq :: PrlTactic
ceqEq (Goal ctx t) =
    case t of
        Eq (CEq m1 n1) (CEq m2 n2) (Uni i) ->
            return $ Result
                       { resultGoals = [ Goal ctx (CEq m1 m2)
                                       , Goal ctx (CEq n1 n2)
                                       ]
                       , resultEvidence = \d ->
                           case d of
                             [d1, d2] -> CEQ_EQ d1 d2
                             _ -> error "CEQ.EQ: Invalid evidence!"
                       }
        _ -> fail "CEQ.EQ does not apply"

ceqRefl :: PrlTactic
ceqRefl (Goal ctx t) =
    case t of
        CEq m n ->
            if m == n
            then return $ Result
                     { resultGoals = []
                     , resultEvidence = \d -> case d of
                                                [] -> CEQ_REFL
                                                _ -> error "CEQ.REFL: Invalid evidence!"
                     }
            else fail "CEQ.REFL: Failed."
        _ -> error "CEQ.REFL does not apply."

ceqStep :: PrlTactic
ceqStep (Goal ctx t) =
    case t of
        CEq m n ->
            case parallelStep m of
              Just m -> return $ Result
                        { resultGoals = [ Goal ctx (CEq m n) ]
                        , resultEvidence = \d ->
                            case d of
                              [d] -> CEQ_STEP d
                              _ -> error "CEQ.STEP: Invalid evidence!"
                        }
              _ -> fail "CEQ.STEP: Could not step."
        _ -> fail "CEQ.STEP does not apply."

-- * Eq

-- * General

-- * Nat

-- * Per

-- * Pi

-- * Sig

-- * Uni

-- * Unit

#ifdef FLAG_coind
-- * Co/inductive

#endif
