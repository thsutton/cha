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
    | Failed String
  deriving (Eq, Show)

prove :: Term -> Tactic Derivation Goal -> Result
prove thm tac =
    case runTacticM (tac (Goal [] thm)) of
        Right (Tactic.Result {resultGoals=[], resultEvidence=evidence}) ->
            Proved { provedDerivation = evidence []
                   , provedExtract = extract (evidence [])
                   }
        Right (Tactic.Result {resultGoals=goals} ) -> Incomplete goals
        Left e -> Failed e
