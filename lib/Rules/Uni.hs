module Rules.Uni where

import Derivation
import Goal
import Rules.Utils
import Tactic
import Term

-- H >> U(i) = U(i) in U(i + 1)
-- Uses: UNI_EQ
uniEQ :: PrlTactic
uniEQ (Goal ctx t) =
    case t of
        Eq (Uni i) (Uni j) (Uni k)
          | i == j && i + 1 == k -> return $ Result
              { resultGoals = []
              , resultEvidence = \d -> case d of
                  [] -> UNI_EQ
                  _ -> error "UNI.EQ: Invalid evidence!"
              }
        _ -> fail "UNI.EQ does no apply."

-- H >> A = B in U(i + 1)
--   H >> A = B in U(i)
-- Uses: CUMULATIVE
uniCUMULATIVE :: PrlTactic
uniCUMULATIVE (Goal ctx t) =
  case t of
    Eq a b (Uni i) | i > 0 -> return $ Result
        { resultGoals = [ Goal ctx (Eq a b (Uni $ 1 - i)) ]
        , resultEvidence = \d -> case d of
            [d] -> CUMULATIVE d
            _ -> error "UNI.CUMULATIVE: Invalid evidence!"
        }
    _ -> fail "UNI.CUMULATIVE does not apply."
