module Rules.Nat where

import Derivation
import Goal
import Rules.Utils
import Tactic
import Term

natEQ :: PrlTactic
natEQ (Goal ctx t) =
    case t of
      Eq Nat Nat (Uni i) -> return $ Result
          { resultGoals = []
          , resultEvidence = \d -> case d of
              [] -> NAT_EQ
              _ -> error "NAT.EQ: Invalid evidence!"
          }
      _ -> fail "NAT.EQ does not apply."

natINTRO :: PrlTactic
natINTRO (Goal ctx t) =
    case t of
      Nat -> return $ Result
          { resultGoals = []
          , resultEvidence = \d -> case d of
              [] -> NAT_INTRO
              _ -> error "NAT.: Invalid evidence!"
          }
      _ -> fail "NAT.INTRO does not apply."

natELIM :: Target -> PrlTactic
natELIM i (Goal ctx t) =
    case t of
      Eq Nat Nat (Uni i) -> return $ Result
          { resultGoals = []
          , resultEvidence = \d -> case d of
              _ -> error "NAT.ELIM: Invalid evidence!"
          }
      _ -> fail "NAT.ELIM does not apply."

natZEROEQ :: PrlTactic
natZEROEQ (Goal ctx t) =
    case t of
      Eq Zero Zero Nat -> return $ Result
          { resultGoals = []
          , resultEvidence = \d -> case d of
              [] -> ZERO_EQ
              _ -> error "NAT.ZEROEQ: Invalid evidence!"
          }
      _ -> fail "NAT.ZEROEQ does not apply."

natSUCCEQ :: PrlTactic
natSUCCEQ (Goal ctx t) =
    case t of
      Eq (Succ m) (Succ n) Nat -> return $ Result
          { resultGoals = [ Goal ctx (Eq m n Nat) ]
          , resultEvidence = \d -> case d of
              [d] -> SUCC_EQ d
              _ -> error "NAT.SUCCEQ: Invalid evidence!"
          }
      _ -> fail "NAT.SUCCEQ does not apply."

natNATRECEQ :: PrlTactic
natNATRECEQ (Goal ctx t) =
    case t of
      Eq (NatRec n1 z1 s1) (NatRec n2 z2 s2) a -> return $ Result
          { resultGoals = [ Goal ctx (Eq n1 n2 Nat)
                          , Goal ctx (Eq z1 z2 a)
                          , Goal ((lift 0 1 a) <:> (Nat <:> ctx)) (Eq s1 s2 (lift 0 2 a))
                          ]
          , resultEvidence = \d -> case d of
              [d1, d2, d3] -> NATREC_EQ d1 d2 d3
              _ -> error "NAT.NATRECEQ: Invalid evidence!"
          }
      _ -> fail "NAT.NATRECEQ does not apply."
