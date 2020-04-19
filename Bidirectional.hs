module Bidirectional
  ( Judgment
  , InferenceRule(..)
  , Derivation(..)
  , checkDerivation
  , inferWith
  , inferWithLog  -- facilates debug process
  , inferWithLogSorted
  ) where

import           ABT
import           Control.Applicative (Applicative (..))
import           Control.Monad       (ap, liftM, join, mapM_, mapM)
import           Data.List           (intercalate, sortBy)
import           Data.Maybe          (isJust, listToMaybe)
import           Data.Ord            (comparing)
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
    mapM_ mergeMatch $
      zipWith match (map judgment (derivePremise derivation)) (premises useRule)
      -- next we check the premises' derivation, recursively
    mapM_ checkDerivation_ (derivePremise derivation)

checkDerivation :: Derivation -> Bool
checkDerivation d = isJust $ fst $ runState (checkDerivation_ d) ignorance

tryInferWithRule :: Judgment -> InferenceRule -> State [Judgment]
j `tryInferWithRule` (Rule prems concl name) = do
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
  liftBacktrack $ writeLog $ "Current Goal: $" ++ show j ++ "$\n"
  r <- caseSplit rules  -- use of the backtracking functionality
  -- liftBacktrack $ writeLog $ "Tries to use rule: $" ++ show r ++ "$\n"
  r <- liftBacktrack $ getFresh r  -- avoids clash
  liftBacktrack $ writeLog $ "R " ++ name r ++ " : $" ++ show r ++ "$\n"
  goals <- liftBacktrack $ j `tryInferWithRule` r
  goalDerivations <- inferGoals goals rules
  j <- liftBacktrack $ metaSubstituteFromState j
  return $ Derivation r goalDerivations j

inferWith :: Judgment -> [InferenceRule] -> Maybe Derivation
j `inferWith` rules = listToMaybe [ x | (Just x, kn) <- runStateBacktrack (j `inferWith_` rules) ignorance]

helper (Just d,  kn) = "Succeeded with tree $$" ++ show d ++ "$$ and logstring $$" ++ show kn ++ "$$\n\n"
helper (Nothing, kn) = "Failed with logstring $$" ++ show kn ++ "$$\n\n"

inferWithLog :: Judgment -> [InferenceRule] -> String
j `inferWithLog` rules = intercalate "\\newpage\nNext case:\n" $ map helper $ runStateBacktrack (j `inferWith_` rules) ignorance

inferWithLogSorted :: Judgment -> [InferenceRule] -> String
j `inferWithLogSorted` rules = intercalate "\\newpage\nNext case:\n" $ map helper $ sortBy (comparing len) $ runStateBacktrack (j `inferWith_` rules) ignorance
  where len = negate . length . logstring . snd
        -- negate to reverse the ordering because we want the long ones first
