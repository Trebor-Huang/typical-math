module Match
  ( match
  ) where

import           ABT
import           Utilities (mergeAssoc, mergeAssocs)

match :: ABT -> ABT -> Maybe [(String, ABT)]
-- match expr pattern ~> association list of meta-vars and expr's
-- in principle, the matched meta-vars should have no closure (Shift 0).
match e (MetaVar n (Shift 0)) = Just [(n, e)]
match _ (MetaVar _ _) = Nothing
match (Var x) (Var y)
  | x == y = Just []
  | x /= y = Nothing
match (Node n args) (Node n' args')
  | n == n' -- dark magic typing... TODO Look into this further
   = mergeAssocs =<< mapM (uncurry match) (zip args args')
match (Bind e) (Bind e') = match e e'
match (MetaVar _ _) _ = Nothing

-- TODO: optionally implement unification
{--
unify :: [(ABT, ABT)] -> Maybe [(ABT, ABT)]
-- unify equations ~> substitutions
unify ((t, u) : eqs)  = if t==u then unify eqs else case (t,u) of
    (Node f args, Node g args') -> if f==g && length args == length args'
        then unify (zip args args')
        else Nothing
    (Var x, Var y) -> if x==y then Just [] else Nothing
--}
