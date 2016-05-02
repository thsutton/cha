-- |

module Rules.Ceq where

import Derivation
import Goal
import Interp
import Rules.Utils
import Tactic
import Term

-- * Ceq

ceqEQ :: PrlTactic
ceqEQ (Goal ctx t) =
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

ceqMEMEQ :: PrlTactic
ceqMEMEQ (Goal ctx t) =
    case t of
        Eq TT TT (CEq m n) ->
            return $ Result
                { resultGoals = [ Goal ctx (CEq m n) ]
                , resultEvidence = \d -> case d of
                    [d] -> CEQ_MEM_EQ d
                    _ -> error "Ceq.MEMEQ: Invalid evidence!"
                }
        _ -> fail "CEQ.MEMEQ does not apply"

ceqSYM :: PrlTactic
ceqSYM (Goal ctx t) =
    case t of
        CEq m n -> return $ Result
            { resultGoals = [ Goal ctx (CEq n m) ]
            , resultEvidence = \d -> case d of
                [d] -> CEQ_SYM d
                _ -> error "Ceq.SYM: Invalid evidence!"
            }

-- H >> [a/x]C
--   H >> a ~ b
--   H >> [b/x]C
-- Uses: CEQ_SUBST
-- Note: the first tactic should be a ~ b and the second should C
ceqSUBST :: Term -> Term -> PrlTactic
ceqSUBST eq pat (Goal ctx t) =
    case eq of
        CEq m n | subst m 0 pat == t -> return $ Result
            { resultGoals = [ Goal ctx eq
                            , Goal ctx (subst n 0 pat)
                            ]
            , resultEvidence = \d -> case d of
                [d1, d2] -> CEQ_SUBST pat d1 d2
                _ -> error "Ceq.SUBST: Invalid evidence!"
            }
        _ -> fail "CEQ.SUBST does not apply."


ceqREFL :: PrlTactic
ceqREFL (Goal ctx t) =
    case t of
        CEq m n | m == n ->
            return $ Result
                { resultGoals = []
                , resultEvidence = \d -> case d of
                    [] -> CEQ_REFL
                    _ -> error "CEQ.REFL: Invalid evidence!"
                }
        CEq m n -> fail "CEQ.REFL: Failed."
        _ -> fail "CEQ.REFL does not apply."

ceqSTEP :: PrlTactic
ceqSTEP (Goal ctx t) =
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
