module Bidirectional
  ( Knowledge(..)
  ) where

import           ABT
import           Control.Applicative (Applicative (..))
import           Control.Monad       (ap, liftM, liftM2, join)
import           Utilities

-- The idea is that knowledge of the assignment of meta-variables,
-- and, by the way, log data is carried through the derivation
-- process, and thus has a monadic feature. This mechanism at work
-- will be explained in the derivation function below.
data Knowledge a
  = Knows
      { assignment :: Maybe [(String, ABT)]
      , logstring  :: String
      , datum      :: Maybe a
      }

instance Functor Knowledge where
  fmap = liftM

instance Applicative Knowledge where
  pure k = Knows {assignment = Just [], logstring = "", datum = Just k}
  (<*>) = ap

instance Monad Knowledge where
  k >>= f = case datum k of  -- Uses pattern matching instead of monadic operations to avoid confusion
    Just d -> Knows{
                assignment = join $ (liftM2 mergeAssoc) (assignment k) (assignment obtained),
                logstring  = logstring k ++ logstring obtained,
                datum      = datum obtained
              }
        where obtained = f d
    Nothing -> fail (logstring k)
  return = pure
  fail l = Knows {assignment = Nothing, logstring = l, datum = Nothing}


-- A judgment susceptible for bidirectional type-checking
-- consists of two parts: one named `input`, and another
-- named `output`. However, These two parts are usually
-- both bound by the context (in the input).
-- In a inference rule, it is required that all the meta-
-- variables in the input part of the premise is obtained
-- by pattern matching with the input of the conclusion.
-- Also, the output of the conclusion is completely obtained
-- by pattern matching with the output of the premise.



