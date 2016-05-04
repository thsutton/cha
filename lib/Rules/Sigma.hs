module Rules.Sigma where

import Derivation
import Goal
import Rules.Utils
import Tactic
import Term

-- H >> Sig x : A. B = Sig x : A'. B' in U(i)
--   H >> A = A' in U(i)
--   H, x : A >> B = B' in U(i)
-- Uses: SIG_EQ
sigmaEQ :: PrlTactic
sigmaEQ (Goal ctx t) =
    case t of
        Eq (Sigma a b) (Sigma a' b') (Uni i) -> return $ Result
            { resultGoals = [ Goal ctx (Eq a a' (Uni i))
                            , Goal (a <:> ctx) (Eq b b' (Uni i))
                            ]
            , resultEvidence = \d -> case d of
                [d1, d2] -> SIG_EQ d1 d2
                _ -> error "Sigma.EQ: Invalid evidence!"
            }
        _ -> fail "Sigma.EQ does not apply."

-- H >> Sig x : A. B
--   H >> a = a in A
--   H >> [a/x]B
--   H, a : A >> B = B in U(i)
-- Uses: SIG_INTRO
sigmaINTRO :: Universe -> Term -> PrlTactic
sigmaINTRO i w (Goal ctx t) =
    case t of
        Sigma a b -> return $ Result
            { resultGoals = [ Goal ctx (Eq w w a)
                            , Goal ctx (subst w 0 b)
                            , Goal (a <:> ctx) (Eq b b (Uni i))
                            ]
            , resultEvidence = \d -> case d of
                [d1, d2, d3] -> SIG_INTRO i w d1 d2 d3
                _ -> error "Sigma.INTRO: Invalid evidence!"
            }
        _ -> fail "Sigma.INTRO does not apply."

-- H >> C
--   H(i) = Sig x : A. B
--   H, x : A, y : B >> C
-- Uses: SIG_ELIM
sigmaELIM :: Target -> PrlTactic
sigmaELIM target (Goal ctx t) =
  case nth (irrelevant t) target ctx of
      Just (Sigma a b) -> return $ Result
          { resultGoals = [ Goal (b <:> (a <:> ctx)) t]
          , resultEvidence = \d -> case d of
              [d] -> SIG_ELIM target d
              _ -> error "Sigma.ELIM: Invalid evidence!"
          }
      _ -> fail "Sigma.ELIM does not apply."

-- H >> pair(a; b) = pair(a'; b') in Sig x : A. B
--  H >> a = a' in A
--  H >> b = b' in [a/x]B
--  H, x : A >> B = B in U(i)
-- Uses: PAIR_EQ
sigmaPAIREQ :: Universe -> PrlTactic
sigmaPAIREQ i (Goal ctx t) =
    case t of
        Eq (Pair m1 n1) (Pair m2 n2) (Sigma a b) -> return $ Result
            { resultGoals = [ Goal ctx (Eq m1 m2 a)
                            , Goal ctx (Eq n1 n2 (subst m1 0 b))
                            , Goal (a <:> ctx) (Eq b b (Uni i))
                            ]
            , resultEvidence = \d -> case d of
                [d1, d2, d3] -> PAIR_EQ i d1 d2 d3
                _ -> error "Sigma.PAIREQ: Invalid evidence!"
            }
        _ -> fail "Sigma.PAIREQ does not apply."

-- H >> fst(a) = fst(a') in A
--   H >> a = a' in Sig x : A. B
-- Uses: FST_EQ
-- Note that the supplied term should be Sig x : A . B
sigmaFSTEQ :: Term -> PrlTactic
sigmaFSTEQ w (Goal ctx t) =
    case (w, t) of
      (Sigma a b, Eq (Fst m1) (Fst m2) a') | a == a' -> return $ Result
          { resultGoals = [ Goal ctx (Eq m1 m2 w)
                          ]
          , resultEvidence = \d -> case d of
              [d] -> FST_EQ w d
              _ -> error "Sigma.FSTEQ: Invalid evidence!"
          }
      _ -> fail "Sigma.FSTEQ does not apply."

-- H >> snd(a) = snd(a') in B'
--   H >> a = a' in Sig x : A. B
--   H >> [fst(a)/x]B = B' in U(i)
-- Uses: SND_EQ
-- Note that the supplied term should be Sig x : A . B
sigmaSNDEQ :: Universe -> Term -> PrlTactic
sigmaSNDEQ i w (Goal ctx t) =
    case (w, t) of
        (Sigma a b, Eq (Snd m1) (Snd m2) b') -> return $ Result
            { resultGoals = [ Goal ctx (Eq m1 m2 w)
                            , Goal ctx (Eq (subst (Fst m1) 0 b) b' (Uni i))
                            ]
            , resultEvidence = \d -> case d of
                _ -> error "Sigma.SNDENV: Invalid evidence!"
            }
        _ -> fail "Sigma.SNDEQ does not apply."
