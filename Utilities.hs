module Utilities
  ( mergeAssoc
  , mergeAssocs
  ) where

import           Control.Monad (foldM, join, liftM2, mapM)
import           ABT (MetaName, ABT, metaSubstitute)

-- utilities
mergeAssoc ::
     (Eq key, Eq value)
  => [(key, value)]
  -> [(key, value)]
  -> Maybe [(key, value)]
mergeAssoc [] assoc = Just assoc
mergeAssoc ((k, v):as) assoc =
  (append (k, v) assoc) >>= (\assoc' -> mergeAssoc as assoc')
  where
    append ::
         (Eq key, Eq value)
      => (key, value)
      -> [(key, value)]
      -> Maybe [(key, value)]
    append (k, v) assoc
      | k `elem` (map fst assoc) =
        case v == snd (head (filter ((== k) . fst) assoc)) of
          True  -> Just assoc
          False -> Nothing
      | otherwise = Just ((k, v) : assoc)

mergeAssocs :: (Eq key, Eq value) => [[(key, value)]] -> Maybe [(key, value)]
mergeAssocs asss = join $ foldM (liftM2 mergeAssoc) (Just []) (map Just asss)

substituteEqs :: [(ABT, ABT)] -> [(MetaName, ABT)] -> [(ABT, ABT)]
substituteEqs eqs subs =
  map (\(e1, e2) -> (metaSubstitute e1 subs, metaSubstitute e2 subs)) eqs
