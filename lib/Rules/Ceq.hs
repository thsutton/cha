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

ceqREFL :: PrlTactic
ceqREFL (Goal ctx t) =
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
