module Rules.Unit where

import Derivation
import Goal
import Rules.Utils
import Tactic
import Term

-- H >> unit = unit in U(i)
-- Uses: UNIT_EQ
unitEQ :: PrlTactic
unitEQ (Goal ctx t) =
    case t of
        Eq Unit Unit (Uni i) -> return $ Result
            { resultGoals = []
            , resultEvidence = \d -> case d of
                [] -> UNIT_EQ
                _ -> error "UNIT.EQ: Invalid evidence!"
            }
        _ -> fail "UNIT.EQ does not apply."

-- H >> unit
-- Uses: UNIT_INTRO
unitINTRO :: PrlTactic
unitINTRO (Goal ctx t) =
    case t of
        Unit -> return $ Result
            { resultGoals = []
            , resultEvidence = \d -> case d of
                [] -> UNIT_INTRO
                _ -> error "UNIT.INTRO: Invalid evidence!"
            }
        _ -> fail "UNIT.INTRO does not apply."

-- H >> tt = tt in unit
-- Uses: TT_EQ
unitTTEQ :: PrlTactic
unitTTEQ (Goal ctx t) =
    case t of
        Eq TT TT Unit -> return $ Result
            { resultGoals = []
            , resultEvidence = \d -> case d of
                [] -> TT_EQ
                _ -> error "UNIT.TTEQ: Invalid evidence!"
            }
        _ -> fail "UNIT.TTEQ does not apply."
