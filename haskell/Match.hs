module Match where

import ABT

-- utilities
mergeAssoc :: (Eq key, Eq value) => [(key, value)] -> [(key, value)] -> Maybe [(key, value)]


match :: ABT -> ABT -> Maybe [(ABT, ABT)]
-- match expr pattern ~> association list of meta-vars and expr's
-- in principle, the matched meta-vars should have no closure (Shift 0).
match (Var x)   (Var y)     | x == y = Just []
                            | x /= y = Nothing
--match (Node n args) (Node n' args') | n == n' = ??  -- Maybe >>= Assoc
-- TODO

-- TODO: optionally implement unification
