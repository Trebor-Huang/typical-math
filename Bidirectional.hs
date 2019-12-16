module Bidirectional
  ( Judgment
  , InferenceRule(..)
  , Derivation(..)
  , checkDerivation
  , inferWith
  ) where

import           ABT
import           Control.Applicative (Applicative (..))
import           Control.Monad       (ap, liftM, join, mapM_, mapM)
import           Match               (match, unify)
import           Utilities
import           Knowledge


checkDerivation_ :: Derivation -> State ()
-- checks if the derivation is valid
checkDerivation_ derivation = do
  -- we first match the rule's conclusion
  useRule <- getFresh (rule derivation)
  mergeMatch (match (judgment derivation) (conclusion useRule))
  -- then we check the premises one by one
  if length (premises useRule) /= length (derivePremise derivation) then
    panic "check     : The number of premises of a derivation is wrong;"
  else do
    -- first we need to ensure that the premises are in the correct form
    -- as asserted by the `useRule`
    mapM_ (mergeMatch . (uncurry match))
      (zip (map judgment (derivePremise derivation)) (premises useRule))
      -- next we check the premises' derivation, recursively
    currentState <- get
    mapM_ checkDerivation_ (derivePremise derivation)

checkDerivation :: Derivation -> Bool
checkDerivation d = case runState (checkDerivation_ d) ignorance of
  (Just (), _) -> True
  (Nothing, _) -> False


tryInferWithRule :: Judgment -> InferenceRule -> State [Judgment]
j `tryInferWithRule` (Rule prems concl) = do
  mergeMatch (unify [(j, concl)])
  mapM metaSubstituteFromState prems


getGoalsAndContinuation :: Judgment -> InferenceRule -> (State [Judgment], ([Derivation] -> State Derivation))
getGoalsAndContinuation j r =
  ( (do writeLog ("Inferring : " ++ show j ++ " using rule: " ++ show r ++ "\n")
        rf <- getFresh r
        tryInferWithRule j rf),
    \goalDerivations ->
      (do writeLog ("Continue Inferring " ++ show j ++ " using rule: " ++ show r ++ "\n")
          j' <- metaSubstituteFromState j
          writeLog ("Finished Inferring " ++ show j)
          return $ Derivation r goalDerivations j'))

inferGoals :: [Judgment] -> [InferenceRule] -> State (Backtrack [Derivation])
inferGoals []     rules = return [[]]
inferGoals (j:js) rules = undefined

inferWith_ :: Judgment -> [InferenceRule] -> Backtrack (State Derivation)
-- A backtracking tree-builder
-- I've adopter rather long variable names here
j `inferWith_` rules = do
  -- remember to do metasubstitution at the right time!
  undefined

inferWith :: Judgment -> [InferenceRule] -> Maybe Derivation
j `inferWith` rules = case [ x | Just x <- undefined] of
  (d: ds) -> Just d  -- Hm. Should we throw error on non-singletons?
  []      -> Nothing
