{-# LANGUAGE CPP #-}
module Term where

import           Control.Applicative
import           Control.Monad.State hiding (lift)
import           Data.Functor
import           Data.Maybe          (fromMaybe)
import           Data.Monoid         hiding (Sum)
import qualified Data.Set            as Set

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

data PrSt = PrSt { nameSupply :: [String], nameStack :: [String] }

newName :: State PrSt String
newName = do
  PrSt (n:n') s <- get
  put (PrSt n' (n:s))
  return n

boundName :: Int -> State PrSt String
boundName i = do
  s <- gets nameStack
  case lookup i (zip [0..] s) of
    Just n -> return n
    Nothing -> newName

pretty :: Term -> String
pretty t = pretty' names t
  where
    names = [0..] >>= \n -> [ x <> (replicate n '\'') | x <- ["x","y","z"]]
    names' = (\n -> "x_" <> show n) <$> [1..]

pretty' :: [String] -> Term -> String
pretty' supply t = evalState (prettyPrint t) (PrSt supply [])

scope :: State PrSt String -> State PrSt String
scope sub = do
  s <- get
  n <- newName
  t <- sub
  put s
  return $ n <> "." <> t

prettyPrint :: Term -> State PrSt String
prettyPrint t =
    case t of
      Var j -> boundName j
      Lam b -> (\b -> "lambda(" <> b <> ")") <$> scope (prettyPrint b)
      Ap f a -> do
             f' <- prettyPrint f
             a' <- prettyPrint a
             return $ "(" <> f' <> " " <> a' <> ")"
      Pi a b -> do
             a' <- prettyPrint a
             b' <- scope (prettyPrint b)
             return $ "Pi(" <> a' <> "; " <> b' <> ")"
      Pair a b -> do
             a' <- prettyPrint a
             b' <- prettyPrint b
             return $ "(" <> a' <> "; " <> b' <> ")"
      Fst p -> (\b -> "fst(" <> b <> ")") <$> prettyPrint p
      Snd p -> (\b -> "snd(" <> b <> ")") <$> prettyPrint p
      Sigma a b -> do
             a' <- prettyPrint a
             b' <- scope (prettyPrint b)
             return $ "Sigma(" <> a' <> "; " <> b' <> ")"
      Zero -> pure "zero"
      Succ n -> do
             n' <- prettyPrint n
             return $ "succ(" <> n' <> ")"
      NatRec n z s -> do
             n' <- prettyPrint n
             z' <- scope (prettyPrint z)
             s' <- scope (prettyPrint s)
             return ("natrec(" <> n' <> "; "
                                <> z' <> "; "
                                <> s' <> ")")
      Nat -> pure "Nat"
      TT -> pure "TT"
      Unit -> pure "Unit"
      Eq a b t -> do
             a' <- prettyPrint a
             b' <- prettyPrint b
             t' <- prettyPrint t
             return ("eq(" <> a' <> "; " <> b' <> "; " <> t' <> ")")
      CEq a b -> do
             a' <- prettyPrint a
             b' <- prettyPrint b
             return ("ceq(" <> a' <> "; " <> b' <> ")")
      Base -> pure "Base"
      Uni i -> pure ("Uni(" <> show i <> ")")
      Per p -> do
             p' <- scope (scope (prettyPrint p))
             return ("Per(" <> p' <> ")")
      Fix f -> do
             f' <- scope (prettyPrint f)
             return ("fix(f. " <> f' <> ")")

#ifdef FLAG_coind
      --
      -- Lift Sums
      --
      Abort a -> do
        a' <- prettyPrint a
        return $ "abort(" <> a' <> ")"
      InL a -> do
        a' <- prettyPrint a
        return $ "InL(" <> a' <> ")"
      InR a -> do
        a' <- prettyPrint a
        return $ "InR(" <> a' <> ")"
      Sum a b -> do
        a' <- prettyPrint a
        b' <- prettyPrint b
        return $ "Sum(" <> a' <> "; " <> b' <> ")"
      Case a l r -> do
        a' <- prettyPrint a
        l' <- scope (prettyPrint l)
        r' <- scope (prettyPrint r)
        return $ "case(" <> a' <> "; " <> l' <> "; " <> r' <> ")"
      Void -> pure "Void"

      --
      -- Lift Generic Map
      --
      Map t f e -> do
        t' <- scope (prettyPrint t)
        f' <- scope (prettyPrint f)
        e' <- prettyPrint e
        return $ "map{" <> t' <> "}(" <> f' <> "; " <> e' <> ")"

      --
      -- Lift Co/Inductive Types
      --
      Coi t -> do
        t' <- scope (prettyPrint t)
        return $ "coi(" <> t' <> ")"
      Ind t -> do
        t' <- scope (prettyPrint t)
        return $ "ind(" <> t' <> ")"
      Fold t e -> do
        t' <- scope (prettyPrint t)
        e' <- prettyPrint e
        return $ "fold{" <> t' <> "}(" <> e' <> ")"
      Rec t r e -> do
            t' <- scope (prettyPrint t)
            r' <- scope (prettyPrint r)
            e' <- prettyPrint e
            return $ "rec{" <> t' <> "}(" <> r' <> "; " <> e' <> ")"

      Unfold t e -> do
        t' <- scope (prettyPrint t)
        e' <- prettyPrint e
        return $ "unfold{" <> t' <> "}(" <> e' <> ")"
      Gen t r e -> do
        t' <- scope (prettyPrint t)
        r' <- scope (prettyPrint r)
        e' <- prettyPrint e
        return $ "gen{" <> t' <> "}(" <> r' <> "; " <> e' <> ")"
#endif

lift :: Int -> Int -> Term -> Term
lift target i tt =
    case tt of
      Var j | j < target -> Var j
            | otherwise  -> Var (j + i)
      Lam b -> Lam (liftBy 1 b)
      Ap f a -> Ap (lft f) (lft a)
      Pi a b -> Pi (lft a) (liftBy 1 b)

      Pair a b -> Pair (lft a) (lft b)
      Fst p -> Fst (lft p)
      Snd p -> Snd (lft p)
      Sigma a b -> Sigma (lft a) (liftBy 1 b)

      Zero -> Zero
      Succ n -> Succ (lft n)
      NatRec n z s -> NatRec (lft n) (lft z)
                             (liftBy 2 s)
      Nat -> Nat

      TT -> TT
      Unit -> Unit
      Eq a b t -> Eq (lft a) (lft b) (lft t)
      CEq a b -> CEq (lft a) (lft b)
      Base -> Base
      Uni i -> Uni i
      Per per -> Per (liftBy 2 per)
      Fix e -> Fix (liftBy 1 e)

#ifdef FLAG_coind
      --
      -- Lift Sums
      --
      Abort a -> Abort (lft a)
      InL a -> InL (lft a)
      InR a -> InR (lft a)
      Sum a b -> Sum (lft a) (lft b)
      Case a l r -> Case (lft a) (liftBy 1 l) (liftBy 1 r)
      Void -> Void

      --
      -- Lift Generic Map
      --
      Map t f e -> Map (liftBy 1 t) (liftBy 1 f) (lft e)

      --
      -- Lift Co/Inductive Types
      --
      Fold t e -> Fold (liftBy 1 t) (lft e)
      Rec t r e -> Rec (liftBy 1 t) (liftBy 1 r) (lft e)
      Ind t -> Ind (liftBy 1 t)
      Unfold t e -> Unfold (liftBy 1 t) (lft e)
      Gen t r e -> Gen (liftBy 1 t) (liftBy 1 r) (lft e)
      Coi t -> Coi (liftBy 1 t)
#endif
  where
    lft t = liftBy 0 t
    liftBy n t = lift (target + n) i t

lower :: Int -> Int -> Term -> Term
lower target i tt =
    case tt of
      Var j | j < target -> Var j
            | otherwise -> Var (j - i)
      Lam b -> Lam (lowerBy 1 b)
      Ap f a -> Ap (lwr f) (lwr f)
      Pi a b -> Pi (lwr a) (lowerBy 1 b)

      Pair a b -> Pair (lwr a) (lwr b)
      Fst p -> Fst (lwr p)
      Snd p -> Snd (lwr p)
      Sigma a b -> Sigma (lwr a) (lowerBy 1 b)

      Zero -> Zero
      Succ n -> Succ (lwr n)
      NatRec n z s -> NatRec (lwr n)
                             (lwr z)
                             (lowerBy 2 s)

      TT -> TT
      Unit -> Unit

      Eq a b t -> Eq (lwr a) (lwr b) (lwr t)
      CEq a b -> CEq (lwr a) (lwr b)
      Base -> Base
      Uni i -> Uni i
      Per per -> Per (lowerBy 2 per)
      Fix e -> Fix (lowerBy 1 e)

#ifdef FLAG_coind
      Abort a -> Abort (lwr a)
      InL a -> InL (lwr a)
      InR a -> InR (lwr a)
      Sum a b -> Sum (lwr a) (lwr b)
      Case a l r -> Case (lwr a) (lowerBy 1 l) (lowerBy 1 r)
      Void -> Void

      Map t f e -> Map (lowerBy 1 t) (lowerBy 1 f) (lwr e)

      Fold t e -> Fold (lowerBy 1 t) (lwr e)
      Rec t r e -> Rec (lowerBy 1 t) (lowerBy 1 r) (lwr e)
      Ind t -> Ind (lowerBy 1 t)
      Unfold t e -> Unfold (lowerBy 1 t) (lwr e)
      Gen t r e -> Gen (lowerBy 1 t) (lowerBy 1 r) (lwr e)
      Coi t -> Coi (lowerBy 1 t)
#endif
  where
    lowerBy n t = lower (target + n) i t
    lwr t = lowerBy 0 t

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
      Lam b -> Lam (lifted b)
      Ap f a -> Ap (subst v i f) (subst v i a)
      Pi a b -> Pi (subst v i a) (lifted b)

      Pair a b -> Pair (subst v i a) (subst v i b)
      Fst p -> Fst (subst v i p)
      Snd p -> Snd (subst v i p)
      Sigma a b -> Sigma (subst v i a) (lifted b)

      Zero -> Zero
      Succ e -> Succ (subst v i e)
      NatRec n z s -> NatRec (subst v i n)
                             (subst v i z)
                             (substBy 2 s)
      Nat -> Nat

      TT -> TT
      Unit -> Unit

      Eq a b t -> Eq (subst v i a) (subst v i b) (subst v i t)
      CEq a b -> CEq (subst v i a) (subst v i b)
      Base -> Base
      Uni i -> Uni i
      Per per -> Per (substBy 2 per)
      Fix f -> Fix (lifted f)

#ifdef FLAG_coind
      Abort a -> Abort (subst v i a)
      InL a -> InL (subst v i a)
      InR a -> InR (subst v i a)
      Sum a b -> Sum (subst v i a) (subst v i b)
      Case a l r -> Case (subst v i a) (lifted l) (lifted r)
      Void -> Void
      Map t f e -> Map (lifted t) (lifted f) (subst v i e)

      Fold t e -> Fold (lifted t) (subst v i e)
      Rec t r e -> Rec (lifted t) (lifted r) (subst v i e)
      Ind t -> Ind (lifted t)
      Unfold t e -> Unfold (lifted t) (subst v i e)
      Gen t r e -> Gen (lifted t) (lifted r) (subst v i e)
      Coi t -> Coi (lifted t)
#endif
  where
    lifted t = substBy 1 t
    substBy n t = subst (lift 0 n v) (i + n) t

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

          Fold t e -> go (c + 1) t <> go c e
          Rec t r e -> go (c + 1) t <> go (c + 1) r <> go c e
          Ind t -> go (c + 1) t

          Unfold t e -> go (c + 1) t <> go c e
          Gen t r e -> go (c + 1) t <> go (c + 1) r <> go c e
          Coi t -> go (c + 1) t
#endif
