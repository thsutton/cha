module Term where

import           Data.Monoid hiding (Sum)
import qualified Data.Set    as Set

-- | Terms of the language.
data Term
    = Var Int -- Variable

    | Lam Term -- Abstraction term
    | Ap Term Term -- Application term. BINDS
    | Pi Term Term -- Dependant function type. BINDS

    | Pair Term Term -- Tuple term
    | Fst Term -- First projection term
    | Snd Term -- Second projection term
    | Sigma Term Term -- Dependant pair type. BINDS

    | TT -- Unit term
    | Unit -- Unit type

    | InL Term -- Left injection term
    | InR Term -- Right injection term
    | Sum Term Term -- Sum type
    | Case Term Term Term -- Case term. BINDS
    | Void -- Void type

    | Fold Term -- Fold term
    | Rec Term Term -- Recursor term. BINDS
    | Ind Term -- Inductive types. BINDS

    | Unfold Term -- Unfold term
    | Gen Term Term -- Generator term. BINDS
    | Coi Term -- Coinductive types. BINDS

lift :: Int -> Int -> Term -> Term
lift target i tt =
    case tt of
      Var j | j < target -> Var j
            | otherwise  -> Var (j + i)
      Lam b -> Lam (lift (target + 1) i b)
      Ap f a -> Ap (lift target i f) (lift target i a)
      Pi a b -> Pi (lift target i a) (lift (target + 1) i b)
      Pair a b -> Pair (lift target i a) (lift target i b)
      Fst p -> Fst (lift target i p)
      Snd p -> Snd (lift target i p)
      Sigma a b -> Sigma (lift target i a) (lift (target + 1) i b)
      TT -> TT
      Unit -> Unit
      InL a -> InL (lift target i a)
      InR a -> InR (lift target i a)
      Sum a b -> Sum (lift target i a) (lift target i b)
      Case a l r -> Case (lift target i a) (lift (target + 1) i l) (lift (target + 1) i r)
      Void -> Void
      Fold e -> Fold (lift target i e)
      Rec r e -> Rec (lift (target + 1) i r) (lift target i e)
      Ind t -> Ind (lift (target + 1) i t)
      Unfold e -> Unfold (lift target i e)
      Gen r e -> Gen (lift (target + 1) i r) (lift target i e)
      Coi t -> Coi (lift (target + 1) i t)

lower :: Int -> Int -> Term -> Term
lower target i tt =
    case tt of
      Var j | j < target -> Var j
            | otherwise -> Var (j - i)
      Lam b -> Lam (lower (target + 1) i b)
      Ap f a -> Ap (lower target i f) (lower target i f)
      Pi a b -> Pi (lower target i a) (lower (target + 1) i b)
      Pair a b -> Pair (lower target i a) (lower target i b)
      Fst p -> Fst (lower target i p)
      Snd p -> Snd (lower target i p)
      Sigma a b -> Sigma (lower target i a) (lower (target + 1) i b)
      TT -> TT
      Unit -> Unit
      InL a -> InL (lower target i a)
      InR a -> InR (lower target i a)
      Sum a b -> Sum (lower target i a) (lower target i b)
      Case a l r -> Case (lower target i a) (lower (target + 1) i l) (lower (target + 1) i r)
      Void -> Void
      Fold e -> Fold (lower target i e)
      Rec r e -> Rec (lower (target + 1) i r) (lower target i e)
      Ind t -> Ind (lower (target + 1) i t)
      Unfold e -> Unfold (lower target i e)
      Gen r e -> Gen (lower (target + 1) i r) (lower target i e)
      Coi t -> Coi (lower (target + 1) i t)

-- | Given a term, an index, and a second term, replace all
-- occurrences of the index in second term with the first term.
subst :: Term -- ^ Value
      -> Int  -- ^ Variable
      -> Term -- ^ Term
      -> Term
subst v i t =
    case t of
      Var j
          | j == i    -> v
          | j > i     -> Var (j - 1)
          | otherwise -> Var j
      Lam b -> Lam (subst (lift 0 1 v) (i + 1) b)
      Ap f a -> Ap (subst v i f) (subst v i a)
      Pi a b -> Pi (subst v i a) (subst (lift 0 1 v) (i + 1) b)
      Pair a b -> Pair (subst v i a) (subst v i b)
      Fst p -> Fst (subst v i p)
      Snd p -> Snd (subst v i p)
      Sigma a b -> Sigma (subst v i a) (subst (lift 0 1 v) (i + 1) b)
      TT -> TT
      Unit -> Unit
      InL a -> InL (subst v i a)
      InR a -> InR (subst v i a)
      Sum a b -> Sum (subst v i a) (subst v i b)
      Case a l r -> Case (subst v i a) (subst (lift 0 1 v) (i + 1) l) (subst (lift 0 1 v) (i + 1) r)
      Void -> Void
      Fold e -> Fold (subst v i e)
      Rec r e -> Rec (subst (lift 0 1 v) (i + 1) r) (subst v i e)
      Ind t -> Ind (subst (lift 0 1 v) (i + 1) t)
      Unfold e -> Unfold (subst v i e)
      Gen r e -> Gen (subst (lift 0 1 v) (i + 1) r) (subst v i e)
      Coi t -> Coi (subst (lift 0 1 v) (i + 1) t)

-- | List the free variables in a term.
freevars :: Term -> [Int]
freevars t = Set.toList (go 0 t)
  where
    go c t =
        case t of
          Var i -> if i < c then mempty else Set.singleton (i - c)
          Lam b -> go (c + 1) b
          Ap f a -> go c f <> go c a
          Pi a b -> go c a <> go (c + 1) b
          Pair l r -> go c l <> go c r
          Fst p -> go c p
          Snd p -> go c p
          Sigma a b -> go c a <> go (c + 1) b
          TT -> mempty
          Unit -> mempty
          InL a -> go c a
          InR b -> go c b
          Sum a b -> go c a <> go c b
          Case e l r -> go c e <> go (c + 1) l <> go (c + 1) r
          Void -> mempty
          Fold e -> go c e
          Rec r e -> go (c + 1) r <> go c e
          Ind t -> go (c + 1) t
          Unfold e -> go c e
          Gen r e -> go (c + 1) r <> go c e
          Coi t -> go (c + 1) t
