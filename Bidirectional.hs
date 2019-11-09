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


class Bidirectional j where
    input  :: j -> ABT
    output :: j -> ABT
    toInferenceFunction :: j -> {- judgment :: -} Knowledge ABT -> Knowledge ABT

