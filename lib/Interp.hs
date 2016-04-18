{-# LANGUAGE CPP           #-}
{-# LANGUAGE DeriveFunctor #-}
module Interp where

import Control.Applicative
import Data.Functor
import Term                as T

data Result t
    = Step t -- ^ The term reduces.
    | Stop -- ^ The term is HNF.
    | Stuck -- ^ The term is stuck.
  deriving (Show, Functor)

step :: Term -> Result Term
step t =
    case t of
      Var i -> Stop
      Lam b -> Stop
      Ap f a -> case step f of
                  Step f' -> Step (Ap f' a)
                  Stuck -> Stuck
                  Stop -> case f of
                           Lam b -> Step (subst a 0 b)
                           _ -> Stuck
      Pi a b -> Stop

      Pair l r -> Stop
      Fst e -> case step e of
                 Step e' -> Step (Fst e')
                 Stuck -> Stuck
                 Stop -> case e of
                          Pair l r -> Step l
                          _ -> Stuck
      Snd e -> case step e of
                 Step e' -> Step (Fst e')
                 Stuck -> Stuck
                 Stop -> case e of
                          Pair l r -> Step r
                          _ -> Stuck
      Sigma a b -> case step a of
                     Step a' -> Step (Sigma a' b)
                     Stuck -> Stuck
                     Stop -> Step (subst a 0 b)

      Zero -> Stop
      Succ s -> Stop
      NatRec n z s -> case step n of
                        Stuck -> Stuck
                        Step n' -> Step (NatRec n' z s)
                        Stop -> case n of
                                  Zero -> Step z
                                  Succ n' -> Step (subst (NatRec n' z s) 0 (subst (lift 0 1 n') 0 s))
                                  _ -> Stuck
      Nat -> Stop

      TT -> Stop
      Unit -> Stop
      Eq a b t -> Stop
      CEq a b -> Stop
      Base -> Stop
      Uni i -> Stop
      Per per -> Stop
      Fix e -> Step (subst (Fix e) 0 e)

#ifdef FLAG_coind
      InL l -> Stop
      InR r -> Stop
      Case e l r -> case step e of
                      Step e' -> Step (Case e' l r)
                      Stuck -> Stuck
                      Stop -> case e of
                               InL v -> Step (subst v 0 l)
                               InR v -> Step (subst v 0 r)
                               _ -> Stuck
      Void -> Stop
      Abort e -> Stuck

      Map t r e -> case t of
                     Var 0 -> Step (subst e 0 r)
                     Unit -> Step e
                     Sigma a b -> Step (Pair (Map a r (Fst e))
                                             (Map (subst a 0 b) r (Snd e)) )
                     Void -> Step (Abort e)
                     Sum a b -> Step (Case e (InL (Map a (lift 2 0 r) (Var 0)) )
                                             (InR (Map b (lift 2 0 r) (Var 0)) ))
                     _ -> Stuck

      Fold t e -> Stop
      Rec t e1 e -> case step e of
                     Step e' -> Step (Rec t e1 e')
                     Stuck -> Stuck
                     Stop -> case e of
                               -- TODO needs some lift or lower or something.
                               Fold t e2 -> Step (subst (Map t (Rec t e1 (Var 0)) e2) 0 e1)
                               _ -> Stuck
      Ind t -> Stop
      Unfold t e -> case step e of
                    Step e' -> Step (Unfold t e')
                    Stuck -> Stuck
                    Stop -> case e of
                             Gen t r e -> Step (Map t (Gen t (lift 1 0 r) (Var 0)) (subst e 0 r))
                             _ -> Stuck
      Gen t r e -> Stop
      Coi t -> Stop
#endif

-- | Take a step and inject the result into 'Maybe'.
safeStep :: Term -> Maybe Term
safeStep t =
    case step t of
      Stuck -> Nothing
      Stop -> Just t
      Step t' -> Just t'

-- | Step the subterms of a term in 'Maybe'.
deepStep :: Term -> Maybe Term
deepStep t = safeStep t >>= \t' ->
    case t' of
      Var i -> pure t'
      Lam b -> Lam <$> deepStep b
      Ap f a -> Ap <$> deepStep f <*> deepStep a
      Pi a b -> Pi <$> deepStep a <*> deepStep b
      Pair a b -> Pair <$> deepStep a <*> deepStep b
      Fst e -> Fst <$> deepStep e
      Snd e -> Snd <$> deepStep e
      Sigma a b -> Sigma <$> deepStep a <*> deepStep b
      Zero -> pure t'
      Succ e -> Succ <$> deepStep e
      NatRec n z s -> NatRec <$> deepStep n <*> deepStep z <*> deepStep s
      Nat -> pure t'
      TT -> pure t'
      Unit -> pure t'
      Eq a b t -> Eq <$> deepStep a <*> deepStep b <*> deepStep t
      CEq a b -> CEq <$> deepStep a <*> deepStep b
      Base -> pure t'
      Uni i -> pure t'
      Per t -> Per <$> deepStep t
      Fix e -> deepStep (subst t 0 e)
#ifdef FLAG_coind
      Abort e -> Abort <$> deepStep e
      InL e -> InL <$> deepStep e
      InR e -> InR <$> deepStep e
      Sum a b -> Sum <$> deepStep a <*> deepStep b
      Case e l r -> Case <$> deepStep e <*> deepStep l <*> deepStep r
      Void -> pure t'

      Map t v f -> Map <$> deepStep t <*> deepStep v <*> deepStep f

      Fold t e -> Fold <$> deepStep t <*> deepStep e
      Rec t r e -> Rec <$> deepStep t <*> deepStep r <*> deepStep e
      Ind t -> Ind <$> deepStep t

      Unfold t e -> Unfold <$> deepStep t <*> deepStep e
      Gen t r e -> Gen <$> deepStep t <*> deepStep r <*> deepStep e
      Coi t -> Coi <$> deepStep t
#endif

-- | Step terms in parallel and under binding forms.
--
-- This is the form that will be used by most tactics.
parallelStep :: Term -> Maybe Term
parallelStep e =
    case deepStep e of
      Just e' | e /= e' -> Just e'
      _                 -> Nothing

-- | Run a term until it reaches head normal form or becomes stuck.
run :: Term -> Maybe Term
run e = case step e of
          Step e' -> run e'
          Stop -> Just e
          Stuck -> Nothing

-- |
normalize :: Term -> Maybe Term
normalize e =
    case parallelStep e of
      Just e' | e == e' -> Just e'
              | otherwise -> normalize e'
      Nothing -> Nothing
