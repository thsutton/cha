module Rules.Eq where

import Derivation
import Goal
import Rules.Utils
import Tactic
import Term

-- H >> (a = b in A) = (a' = b' in A') in U(i)
--   H >> A = A' in U(i)
--   H >> a = a' in A
--   H >> b = b' in A'
-- Uses: EQ_EQ
eqEQ :: PrlTactic
eqEQ (Goal ctx t) =
    case t of
        Eq (Eq m1 n1 a1) (Eq m2 n2 a2) (Uni i) ->
            return $ Result
                { resultGoals = [ Goal ctx (Eq a1 a2 (Uni i))
                                , Goal ctx (Eq m1 m2 a1)
                                , Goal ctx (Eq n1 n2 a1)
                                ]
                , resultEvidence = \d ->
                    case d of
                        [d1, d2, d3] -> EQ_EQ d1 d2 d3
                        _ -> error "Eq.EQ: Invalid evidence!"
                }
        _ -> fail "Eq.EQ does not apply."

-- H >> tt = tt in (a = b in A)
--   H >> a = b in A
-- Uses: EQ_MEM_EQ
eqMEMEQ :: PrlTactic
eqMEMEQ (Goal ctx t) =
    case t of
        Eq TT TT (Eq m n a) -> return $ Result
            { resultGoals = [ Goal ctx (Eq m n a) ]
            , resultEvidence = \d -> case d of
                [d] -> EQ_MEM_EQ d
                _ -> error "Eq.MEMEQ: Invalid evidence!"
            }
        _ -> fail "Eq.MEMEQ does not apply."


-- H >> a = b in A
--   H >> b = a in A
-- Uses: EQ_SYM
eqSYM :: PrlTactic
eqSYM (Goal ctx t) =
    case t of
      Eq m n a -> return $ Result
          { resultGoals = [ Goal ctx (Eq n m a) ]
          , resultEvidence = \d -> case d of
              [d] -> EQ_SYM d
              _ -> error "Eq.SYM: Invalid evidence!"
          }
      _ -> fail "Eq.SYM does not apply."

-- H >> [a/x]C
--   H, x : A >> C in U(i)
--   H >> a = b in A
--   H >> [b/x]C
-- Uses: EQ_SUBST
-- Note that first supplied term should be a = b in A and
-- the second one should be C.
eqSUBST :: Universe -> Term -> Term -> PrlTactic
eqSUBST uni eq pat (Goal ctx t) =
    case eq of
      Eq m n a | subst m 0 pat == t -> return $ Result
          { resultGoals = [ Goal (a <:> ctx) (Eq pat pat (Uni uni))
                          , Goal ctx eq
                          , Goal ctx (subst n 0 pat)
                          ]
          , resultEvidence = \d -> case d of
              [d1, d2, d3] -> EQ_SUBST uni pat d1 d2 d3
              _ -> error "Eq.SUBST: Invalid evidence!"
          }
      _ -> fail "Eq.SUBST does not apply."
