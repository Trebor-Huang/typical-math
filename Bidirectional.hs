module Bidirectional
  ( Knowledge(..)
  ) where

import           ABT
import           Control.Applicative (Applicative (..))
import           Control.Monad       (ap, liftM, liftM2, join)
import           Match               (match, unify)
import           Utilities

-- The idea is that knowledge of the assignment of meta-variables,
-- and, by the way, log data is carried through the derivation
-- process, and thus has a monadic feature. This mechanism at work
-- will be explained in the derivation function below.
data Knowledge a
  = Knows
      { assignment :: [(String, ABT)]
      , gensym     :: Int
      , logstring  :: String  -- This should always end with a newline!
      , datum      :: a
      }
    | Panic 
      {
        logstring :: String
      }

instance Functor Knowledge where
  fmap = liftM

instance Applicative Knowledge where
  pure k = Knows {assignment = [], gensym = 0, logstring = "", datum = k}
  (<*>) = ap

instance Monad Knowledge where
  k >>= f = case k of  -- TODO pack this up into a nice monadic expression
    Knows ass gen logs dat -> case f dat of
        Knows ass' gen' logs' dat' -> case mergeAssoc ass ass' of
          Just assoc -> Knows assoc gen' (logs ++ logs') dat'
          Nothing -> Panic (logs ++ logs' ++
            "Assignment merge failed: \n  " ++ show ass ++ 
            "\nand\n  " ++ show ass' ++ 
            "\ncannot be merged.\n")
        Panic logs' -> Panic (logs ++ logs')
    Panic logs -> Panic logs
  return = pure
  fail l = Panic {logstring = l}


-- A judgment susceptible for bidirectional type-checking
-- consists of two parts: one named `input`, and another
-- named `output`. However, These two parts are usually
-- both bound by the context (in the input).
-- In a inference rule, it is required that all the meta-
-- variables in the input part of the premise is obtained
-- by pattern matching with the input of the conclusion.
-- Also, the output of the conclusion is completely obtained
-- by pattern matching with the output of the premise.

-- We try out a more elegant approach, where the judgments are
-- syntactically seperable to input and output parts, but not
-- explicitly marked out. We use a basic form of unification,
-- where meta-variables with closures are always treated as 
-- rigid. If the arrangements of the judgments are correct, the
-- information will propogate through the derivation tree, as if
-- the input/output parts were correcly marked. In this way, a
-- judgment is no different from a ordinary syntactic node:

type Judgment = ABT

-- If this does not work, we will fall back to the traditional
-- bidirectional method instead.

data InferenceRule 
  = Rule 
      { premises   :: [Judgment {- with meta-variable -}]
      , conclusion ::  Judgment {- with meta-variable -}
      }

freeMetaVarInf r = freeMetaVar (conclusion r) ++ concatMap freeMetaVar (premises r)
metaSubstituteInf r subs = Rule (map (`metaSubstitute` subs) (premises r))
  ((conclusion r) `metaSubstitute` subs)

data Derivation
  = Derivation
      { rule          :: InferenceRule
      , derivePremise :: [Derivation {- without meta-variable -}]
      , judgment      :: Judgment    {- without meta-variable -}
      }

getFresh :: InferenceRule -> Knowledge a -> Knowledge InferenceRule
getFresh inf p@(Panic _) = p
getFresh inf k = undefined

checkDerivation :: Derivation -> Knowledge ()
-- checks if the derivation is valid
checkDerivation d = undefined

inferWith :: Judgment -> InferenceRule -> Maybe Derivation
-- turns a judgment into a derivation, given an inference rule
inferWith = undefined
