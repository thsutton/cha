{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE RecordWildCards #-}
module Tactic where

import Control.Applicative
import Control.Monad
import Data.Functor
import Data.Monoid

-- | A backtracking monad implemented with CPS.
newtype TacticM r a = TacticM { cont :: (a -> Either String r) -> Either String r }

instance Functor (TacticM r) where
    fmap f (TacticM cont) = TacticM $ \k -> cont (k . f)

instance Applicative (TacticM r) where
    pure a = TacticM $ \k -> k a
    (TacticM f) <*> (TacticM a) = TacticM $ \k -> f (\fv -> a (\av -> k (fv av)))

instance Alternative (TacticM r) where
    empty = TacticM $ const (Left "")
    (TacticM a) <|> (TacticM b) = TacticM $ \k ->
                                  case a k of
                                    Left _ -> b k
                                    r -> r

instance Monad (TacticM r) where
    return g = TacticM $ \k -> k g
    fail e = TacticM $ const (Left e)
    (TacticM a) >>= f = TacticM $ \k -> a (\av -> (cont $ f av) k)

instance MonadPlus (TacticM r)

runTacticM :: TacticM a a -> Either String a
runTacticM t = cont t $ Right

-- | A 'Result' is a specification of what is left to be proved (the
-- `goals`) and a way of combining derivations which satisfy those
-- requirements into a proof of the original goal.
data Result derivation goal = Result
    { resultEvidence :: [derivation] -> derivation
    , resultGoals    :: [goal]
    }

type Choice derivation goal a = TacticM (Result derivation goal) a

type Tactic derivation goal = goal -> Choice derivation goal (Result derivation goal)

-- * Helpers

-- $ These functions are helpful for implementing low-level tactics.

-- | Glue a derivation together by lining up some pending sub-results
-- with some matching derivations.
--
-- TODO: This function can fail with a pattern match failure.
joinEvidence
    :: ([derivation] -> derivation) -- ^ Build a derivation from the assembled sub-derivations.
    -> [Result derivation goal] -- ^ Results of sub-goals.
    -> [derivation] -- ^ Derivations for sub-goals.
    -> derivation
joinEvidence top subresults ds =
    let
        derivChunks = chunk (fmap (length . resultGoals) subresults) ds
        Just evidence = zipAppOpt (fmap resultEvidence subresults) derivChunks
    in
      top evidence
  where
    chunk :: [Int] -> [derivation] -> [[derivation]]
    chunk []     _  = []
    chunk (i:is) ds = (take i ds) : (chunk is (drop i ds))

-- | Zip a list of functions and a list of values of exactly the same length.
zipAppOpt :: [a -> b] -> [a] -> Maybe [b]
zipAppOpt [] [] = Just []
zipAppOpt [] _  = Nothing
zipAppOpt _  [] = Nothing
zipAppOpt (x:xs) (y:ys) = ((x y) :) <$> zipAppOpt xs ys

-- * Primitive tactics

-- | Trivial tactic which always fails.
failTac :: Tactic derivation goal
failTac _ = mzero

-- | Trivial tactic which always succeeds by passing the goal through unchanged.
idTac :: Tactic derivation goal
idTac goal = return $ (Result
             { resultEvidence = \ds ->
               case ds of
                 [d] -> d
                 [] -> error "ID requires one sub-goal derivation; got none."
                 n -> error ("ID requires one sub-goal derivation; got " <> show (length n) <> ".")
             , resultGoals = [goal]
             })

-- | Apply one tactic or, if it fails, another tactic.
chooseTac :: Tactic d g -> Tactic d g -> Tactic d g
chooseTac t1 t2 goal = (t1 goal) <|> (t2 goal)

-- | Apply one tactic then apply a second to all the subgoals.
next :: Tactic d g -> Tactic d g -> Tactic d g
next t1 t2 goal = do
    Result{resultGoals=goals, resultEvidence=evidence} <- t1 goal
    subresults <- sequence (fmap t2 goals)
    return $ Result
               { resultGoals = concatMap resultGoals subresults
               , resultEvidence = joinEvidence evidence subresults
               }

-- | Apply one tactic, then apply a sequence of tactics to the
-- corresponding subgoals.
--
-- There must be exactly the same number of subtactics and subgoals.
splitTac :: Tactic d g -> [Tactic d g] -> Tactic d g
splitTac t ts goal = do
    Result{resultEvidence=evidence,resultGoals=goals} <- t goal
    let n_goals = length goals
    let n_tacs = length ts
    case zipAppOpt ts goals of
      Nothing ->
          fail ("SPLIT Cannot split " <> show n_goals <> " goals with " <> show n_tacs <> " tactics.")
      Just subresults ->
          do
            subresults <- sequence subresults
            return $ Result { resultGoals = concatMap resultGoals subresults
                            , resultEvidence = joinEvidence evidence subresults
                            }

-- | Apply a tactic over and over until it fails, at which point run identity.
repeatTac :: Tactic d g -> Tactic d g
repeatTac t = chooseTac (t `next` (repeatTac t)) idTac
