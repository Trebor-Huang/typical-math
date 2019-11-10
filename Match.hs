module Match
  ( match
  ) where

import           ABT
import           Utilities (mergeAssoc, mergeAssocs, substituteEqs)

match :: ABT -> ABT -> Maybe [(MetaName, ABT)]
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

unify :: [(ABT, ABT)] -> Maybe [(MetaName, ABT)]
-- unify equations ~> substitutions
--data ABT = Var VarName | Node NodeType [ABT] | Bind ABT | MetaVar MetaName Substitution
deriving (Eq)
unify ((t, t) : eqs) = unify eqs  -- delete
unify ((Var v1, Var v2) : eqs) = 

