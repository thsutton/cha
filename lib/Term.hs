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

    | Zero -- Zero term
    | Succ Term -- Successor term
    | NatRec Term Term Term -- Natural recursion. BINDS
    | Nat -- Natural number type.

    | TT -- Unit term
    | Unit -- Unit type

    | Eq Term Term Term -- Equality proposition.
    | CEq Term Term -- Computational equality.
    | Base -- Type of all terms.
    | Uni Int -- Universe of types smaller than i.
    | Per Term -- PER as type. BINDS
    | Fix Term -- Fix point operator. BINDS

#ifdef FLAG_coind
    | Abort Term -- Nullary sum.
    | InL Term -- Left injection term
    | InR Term -- Right injection term
    | Sum Term Term -- Sum type
    | Case Term Term Term -- Case term. BINDS
    | Void -- Void type

    | Map Term Term Term -- Generic extension. BINDS

    | Fold Term Term -- Fold term
    | Rec Term Term Term -- Recursor term. BINDS
    | Ind Term -- Inductive types. BINDS

    | Unfold Term Term -- Unfold term
    | Gen Term Term Term -- Generator term. BINDS
    | Coi Term -- Coinductive types. BINDS
#endif
  deriving (Show, Eq)

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

      Zero -> Zero
      Succ n -> Succ (lift target i n)
      NatRec n z s -> NatRec (lift target i n) (lift target i z)
                             (lift (target + 2) i s)
      Nat -> Nat

      TT -> TT
      Unit -> Unit
      Eq a b t -> Eq (lift target i a) (lift target i b) (lift target i t)
      CEq a b -> CEq (lift target i a) (lift target i b)
      Base -> Base
      Uni i -> Uni i
      Per per -> Per (lift (target + 2) i per)
      Fix e -> Fix (lift (target + 1) i e)

#ifdef FLAG_coind
      Abort a -> Abort (lift target i a)
      InL a -> InL (lift target i a)
      InR a -> InR (lift target i a)
      Sum a b -> Sum (lift target i a) (lift target i b)
      Case a l r -> Case (lift target i a) (lift (target + 1) i l) (lift (target + 1) i r)
      Void -> Void

      Map t f e -> Map (lift (target + 1) i t) (lift (target + 1) i f) (lift target i e)

      Fold t e -> Fold t (lift target i e)
      Rec t r e -> Rec t (lift (target + 1) i r) (lift target i e)
      Ind t -> Ind (lift (target + 1) i t)
      Unfold t e -> Unfold t (lift target i e)
      Gen t r e -> Gen t (lift (target + 1) i r) (lift target i e)
      Coi t -> Coi (lift (target + 1) i t)
#endif

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

      Zero -> Zero
      Succ n -> Succ (lower target i n)
      NatRec n z s -> NatRec (lower target i n)
                             (lower target i z)
                             (lower (target + 2) i s)

      TT -> TT
      Unit -> Unit

      Eq a b t -> Eq (lower target i a) (lower target i b) (lower target i t)
      CEq a b -> CEq (lower target i a) (lower target i b)
      Base -> Base
      Uni i -> Uni i
      Per per -> Per (lower (target + 2) i per)
      Fix e -> Fix (lower (target + 1) i e)

#ifdef FLAG_coind
      Abort a -> Abort (lower target i a)
      InL a -> InL (lower target i a)
      InR a -> InR (lower target i a)
      Sum a b -> Sum (lower target i a) (lower target i b)
      Case a l r -> Case (lower target i a) (lower (target + 1) i l) (lower (target + 1) i r)
      Void -> Void

      Map t f e -> Map (lower (target + 1) i t) (lower (target + 1) i f) (lower target i e)

      Fold t e -> Fold t (lower target i e)
      Rec t r e -> Rec t (lower (target + 1) i r) (lower target i e)
      Ind t -> Ind (lower (target + 1) i t)
      Unfold t e -> Unfold t (lower target i e)
      Gen t r e -> Gen t (lower (target + 1) i r) (lower target i e)
      Coi t -> Coi (lower (target + 1) i t)
#endif

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

      Zero -> Zero
      Succ e -> Succ (subst v i e)
      NatRec n z s -> NatRec (subst v i n)
                             (subst v i z)
                             (subst (lift 0 2 v) (i + 2) s)
      Nat -> Nat

      TT -> TT
      Unit -> Unit

      Eq a b t -> Eq (subst v i a) (subst v i b) (subst v i t)
      CEq a b -> CEq (subst v i a) (subst v i b)
      Base -> Base
      Uni i -> Uni i
      Per per -> Per (subst (lift 0 2 v) (i + 2) per)
      Fix e -> Fix (subst (lift 0 1 v) (i + 1) e)

#ifdef FLAG_coind
      Abort a -> Abort (subst v i a)
      InL a -> InL (subst v i a)
      InR a -> InR (subst v i a)
      Sum a b -> Sum (subst v i a) (subst v i b)
      Case a l r -> Case (subst v i a) (subst (lift 0 1 v) (i + 1) l) (subst (lift 0 1 v) (i + 1) r)
      Void -> Void
      Map t f e -> Map (subst (lift 0 1 v) (i + 1) t) (subst (lift 0 1 v) (i + 1) f) (subst v i e)

      Fold t e -> Fold t (subst v i e)
      Rec t r e -> Rec t (subst (lift 0 1 v) (i + 1) r) (subst v i e)
      Ind t -> Ind (subst (lift 0 1 v) (i + 1) t)
      Unfold t e -> Unfold t (subst v i e)
      Gen t r e -> Gen t (subst (lift 0 1 v) (i + 1) r) (subst v i e)
      Coi t -> Coi (subst (lift 0 1 v) (i + 1) t)
#endif

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
          Eq a b t -> go c a <> go c b <> go c t
          CEq a b -> go c a <> go c b
          Base -> mempty
          Uni i -> mempty
          Per per -> go (c + 2) per
          Fix e -> go (c + 1) e
#ifdef FLAG_coind
          Abort e -> go c e
          InL a -> go c a
          InR b -> go c b
          Sum a b -> go c a <> go c b
          Case e l r -> go c e <> go (c + 1) l <> go (c + 1) r
          Void -> mempty
          Map t f e -> go (c + 1) t <> go (c + 1) f <> go c e
          Fold t e -> go c e
          Rec t r e -> go (c + 1) r <> go c e
          Ind t -> go (c + 1) t
          Unfold t e -> go c e
          Gen t r e -> go (c + 1) r <> go c e
          Coi t -> go (c + 1) t
#endif
