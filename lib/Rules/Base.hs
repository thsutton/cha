-- |

module Rules.Base where


import Data.List   (nub)
import Data.Monoid

import Derivation
import Goal
import Rules.Utils
import Tactic
import Term

-- | Prove that @base = base in U(i)@ from any assumptions.
--
--  H >> base = base in U(i)
baseEQ :: PrlTactic
baseEQ (Goal ctx t) =
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
baseMEMEQ :: PrlTactic
baseMEMEQ (Goal ctx t) =
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
baseELIMEQ :: Target -> PrlTactic
baseELIMEQ target (Goal ctx t) =
    case nth (irrelevant t) target ctx of
        Just (Eq a b Base) ->
            -- We lift `t` because we've added to the head of `ctx`.
            return $ Result
                   { resultGoals = [Goal (CEq a b <:> ctx) (lift 0 1 t)]
                   , resultEvidence = \d ->
                       case d of
                           [d] -> BASE_ELIM_EQ target d
                           _ -> error "Base.ELIMEQ: Invalid evidence!"

                   }
        _ -> fail "ELIMEQ does not apply."
