module Rules.General where

import Derivation
import Goal
import Rules.Utils
import Tactic
import Term

-- H >> C
--   H(i) = C
-- Uses: VAR
generalHYP :: Target -> PrlTactic
generalHYP target (Goal ctx t) =
    case nth (irrelevant t) target ctx of
        Just t' | t == t' ->
            return $ Result
                { resultGoals = []
                , resultEvidence = \d ->
                    case d of
                        [] -> VAR target
                        _  -> error "General.HYP: Invalid evidence!"
                }
        _ -> fail "General.HYP does not apply."
