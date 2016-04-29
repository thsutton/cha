module Refiner where

import           Derivation
import           Extract
import           Goal
import           Tactic     hiding (Result)
import qualified Tactic     as Tactic
import           Term

data Result
    = Proved { provedDerivation :: Derivation
             , provedExtract    :: Term
             }
    | Incomplete [Goal]
    | Failed
  deriving (Eq, Show)

prove :: Term -> Tactic Derivation Goal -> Result
prove thm tac =
    case runTacticM (tac (Goal [] thm)) of
        Just (Tactic.Result {resultGoals=[], resultEvidence=evidence}) ->
            Proved { provedDerivation = evidence []
                   , provedExtract = extract (evidence [])
                   }
        Just (Tactic.Result {resultGoals=goals} ) -> Incomplete goals
        Nothing -> Failed
