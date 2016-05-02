-- |
-- This module contains the tactics for manipulating goals involving with Pi
-- types.
module Rules.Pi where

import Derivation
import Goal
import Rules.Utils
import Tactic
import Term

-- H >> Pi x : A. B = Pi x : A'. B' in U(i)
--   H >> A = A' in U(i)
--   H, x : A >> B(x) = B'(x) in U(i)
-- Uses: PI_EQ
piEQ :: PrlTactic
piEQ (Goal ctx t) =
    case t of
        Eq (Pi a1 b1) (Pi a2 b2) (Uni i) ->
            return $ Result
                   { resultGoals = [ Goal ctx (Eq a1 a2 (Uni i))
                                   , Goal (a1 <:> ctx) (Eq b1 b2 (Uni i))
                                   ]
                   , resultEvidence = \d ->
                       case d of
                           [d1, d2] -> PI_EQ d1 d2
                           _ -> error "Pi.EQ: Invalid evidence!"
                   }
        _ -> fail "Pi.EQ does not apply."

-- H >> Pi x : A. B
--   H >> A = A in U(i)
--   H, x : A >> B
--
piINTRO :: Universe -> PrlTactic
piINTRO uni (Goal ctx t) =
    case t of
        Pi a b -> return $ Result
                  { resultGoals = [ Goal ctx (Eq a a (Uni uni))
                                  , Goal (a <:> ctx) b
                                  ]
                  , resultEvidence = \d ->
                      case d of
                          [d1, d2] -> PI_INTRO uni d1 d2
                          _ -> error "Pi.INTRO: Invalid evidence!"
                  }
        _ -> fail "Pi.INTRO does not apply."

--
--  H >> C
--   H(i) = Pi x : A. B
--   H >> a = a in A
--   H, [a/x]B >> C
-- Uses: PI_ELIM
piELIM :: Target -> Term -> PrlTactic
piELIM target arg (Goal ctx t) =
    case nth (irrelevant t) target ctx of
        Just (Pi a b) -> return $ Result
          { resultGoals = []
          , resultEvidence = \d ->
              case d of
                  _ -> error "Pi.ELIM: Invalid evidence!"
          }
        _ -> fail "Pi.ELIM does not apply."

