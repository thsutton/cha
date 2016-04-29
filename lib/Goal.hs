module Goal where

import Term

-- | Hypotheses can be hidden when we do not depend on it computationally.
data Visibility
    = Hidden
    | Visible
  deriving (Eq, Show)

type Context = [(Visibility, Term)]

-- | A goal has a 'Context' of hypotheses and a goal 'Term'.
data Goal = Goal { goalContext :: Context
                 , goalTerm    :: Term
                 }
  deriving (Eq, Show)

-- | Retrieve the nth term from a 'Context'.
--
-- If the nth term is hidden and we've asked to omit them we'll get 'Nothing'.
nth :: Bool -- ^ Return a 'Hidden' term?
    -> Int -- ^ Item
    -> Context
    -> Maybe Term
nth irr i ctx =
    case lookup i (zip [0..] ctx) of
        Just (v, t)
            | irr || v == Visible -> Just (lift 0 (i + 1) t)
        _ -> Nothing
