module Bidirectional
  ( Judgment
  , InferenceRule(..)
  , Derivation(..)
  , checkDerivation
  , inferWith
  , inferWith_  -- facilates debug process
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
    panic "The number of premises of a derivation is wrong;\n"
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

-- the two functions below do mutual recursion
-- the first one solves a list of goals sequentially using the second one
-- and the second one solves one goal, and when encountering a list of goals,
-- uses the first function
inferGoals :: [Judgment] -> [InferenceRule] -> StateBacktrack [Derivation]
inferGoals []     rules = return []
inferGoals (j:js) rules = do
  derivation <- j `inferWith_` rules
  js <- liftBacktrack $ mapM metaSubstituteFromState js
  derivations <- inferGoals js rules
  derivation <- liftBacktrack $ metaSubstituteDerFromState derivation
  -- TODO: maybe these substitutions are somehow redundant..?
  return (derivation : derivations)

inferWith_ :: Judgment -> [InferenceRule] -> StateBacktrack Derivation
inferWith_ j rules = do
  r <- caseSplit rules  -- use of the backtracking functionality
  r <- liftBacktrack $ getFresh r  -- avoids clash
  liftBacktrack $ writeLog $ "Tries to use rule: " ++ show r ++ "\n"
  goals <- liftBacktrack $ j `tryInferWithRule` r
  goalDerivations <- inferGoals goals rules
  j <- liftBacktrack $ metaSubstituteFromState j
  return $ Derivation r goalDerivations j

inferWith :: Judgment -> [InferenceRule] -> Maybe Derivation
j `inferWith` rules = case [ x | (Just x, kn) <- runStateBacktrack (j `inferWith_` rules) ignorance] of
  (d: ds) -> Just d  -- Hm. Should we throw error on non-singletons?
  []      -> Nothing
