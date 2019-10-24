module Match where

import ABT
import Control.Monad (foldM, mapM, liftM2, join)

-- utilities
mergeAssoc :: (Eq key, Eq value) => [(key, value)] -> [(key, value)] -> Maybe [(key, value)]
mergeAssoc [] assoc = Just assoc
mergeAssoc ((k,v) : as) assoc = (append (k,v) assoc) >>= (\assoc' -> mergeAssoc as assoc')
    where append :: (Eq key, Eq value) => (key, value) -> [(key, value)] -> Maybe [(key, value)]
          append (k, v) assoc | k `elem` (map fst assoc) =
                    case v == snd ( head (filter ((== k) . fst) assoc) ) of
                        True  -> Just assoc
                        False -> Nothing
                              | otherwise                = Just ((k, v) : assoc)

match :: ABT -> ABT -> Maybe [(ABT, ABT)]
-- match expr pattern ~> association list of meta-vars and expr's
-- in principle, the matched meta-vars should have no closure (Shift 0).
match e m@(MetaVar n _) = Just [(m, e)]
match (Var x)   (Var y)    | x == y = Just []
                           | x /= y = Nothing
match (Node n args) (Node n' args') | n == n' =   -- dark magic typing... TODO Look into this further
    join $ foldM (liftM2 mergeAssoc) (Just []) [ match a a' | (a, a') <- zip args args']
match (Bind e) (Bind e') = match e e'
match (MetaVar _ _) _ = Nothing

-- TODO: optionally implement unification
