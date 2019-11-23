module Match
  ( match
  , unify
--, unify'
  ) where

import           ABT
import           Utilities (mergeAssoc, mergeAssocs, substituteEqs, freeMetaVarEqs)

match :: ABT -> ABT -> Maybe [(MetaName, ABT)]
-- match expr pattern ~> association list of meta-vars and expr's
-- in principle, the matched meta-vars should have no closure (Shift 0).
match e (MetaVar n (Shift 0)) = Just [(n, e)]
match _ (MetaVar _ _) = Nothing
match (Var x) (Var y)
  | x == y = Just []
  | x /= y = Nothing
match (Node n args) (Node n' args')
  | n == n' = mergeAssocs =<< mapM (uncurry match) (zip args args')
match (Bind e) (Bind e') = match e e'
match (MetaVar _ _) _ = Nothing

unify' :: [(ABT, ABT)] -> Maybe [(ABT, ABT)]
-- one cycle of the unification process
unify' [] = Just []
-- Delete / Decompose / Conflict
unify' ((Var v1, Var v2) : eqs) | v1 /= v2  = Nothing
                                | otherwise = Just eqs
unify' ((Bind e1, Bind e2) : eqs) = Just ((e1, e2) : eqs)
unify' ((Node n args, Node n' args') : eqs)
    | n /= n'                     = Nothing
    | length args /= length args' = Nothing
    | otherwise = Just ((zip args args') ++ eqs)
-- Swap
unify' ((v@(Var _),    m@(MetaVar _ (Shift 0))) : eqs) = Just ((m, v) : eqs)
unify' ((n@(Node _ _), m@(MetaVar _ (Shift 0))) : eqs) = Just ((m, n) : eqs)
unify' ((b@(Bind _),   m@(MetaVar _ (Shift 0))) : eqs) = Just ((m, b) : eqs)
-- Eliminate / Check
unify' ((m@(MetaVar n (Shift 0)), expr) : eqs)
  | m `elem` (freeMetaVar expr) = Nothing
  | m `notElem` (freeMetaVarEqs eqs) = Just (eqs ++ [(m, expr)])
  | otherwise = Just ((m, expr) : (substituteEqs eqs [(n, expr)]))
-- The other part of swap : rigid meta-variables
unify' ((m'@(MetaVar _ _), m@(MetaVar _ (Shift 0))) : eqs) = Just ((m, m') : eqs)


unify :: [(ABT, ABT)] -> Maybe [(MetaName, ABT)]
-- unify equations ~> substitutions
-- TODO this currently sees meta-variables with closures as rigid.
-- we may implement a more powerful unification algorithm that
-- helps implicit argument inference.
unify eqs = do
  if done eqs then
    return (clean eqs)
  else do
    next <- unify' eqs
    result <- unify next
    return result
  where done :: [(ABT, ABT)] -> Bool
        done eqs = all helper' eqs && not ((map fst eqs) `occurs` (map snd eqs))
        helper' :: (ABT, ABT) -> Bool
        helper' (MetaVar n (Shift 0), expr) = True
        helper' _ = False
        occurs :: [ABT] -> [ABT] -> Bool
        occurs ms exprs = any (`elem` (concatMap freeMetaVar exprs)) (map clean' ms)
        clean' :: ABT -> ABT
        clean' m@(MetaVar _ (Shift 0)) = m
        clean' _ = error "Panic! The algorithm has something wrong!!"
        clean :: [(ABT, ABT)] -> [(MetaName, ABT)]
        clean = map helper
        helper :: (ABT, ABT) -> (MetaName, ABT)
        helper (MetaVar n (Shift 0), expr) = (n, expr)
        helper _ = error "Panic! The algorithm has something wrong!!"
