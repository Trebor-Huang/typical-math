module Match
  ( match
  , unify
  ) where

import           ABT
import           Utilities (mergeAssoc, mergeAssocs, substituteEqs, freeMetaVarEqs)

match :: ABT -> ABT -> Either String Assignment
-- match expr pattern ~> association list of meta-vars and expr's
-- in principle, the matched meta-vars should have no closure (Shift 0).
match e (MetaVar n (Shift 0)) = Right [(n, e)]
match e m@(MetaVar _ _) = Left $ "Meta-var with closure encountered, matching aborted : " ++ (show e) ++ " against " ++ (show m)
match (Var x) (Var y)
  | x == y = Right []
  | x /= y = Left $ "Variable mismatch: " ++ (show x) ++ " and " ++ (show y)
match (Node n args) (Node n' args')
  | n == n' = helper2 $ mergeAssocs =<< mapM helper (map (uncurry match) (zip args args'))
  where helper (Right r) = Just r
        helper (Left s)  = Nothing
        helper2 (Just a) = Right a
        helper2 Nothing = Left "Conflicting equations."
match (Bind e) (Bind e') = match e e'
match m@(MetaVar _ _) e = Left $ "Metavariables on the wrong side: " ++ (show m) ++ " against " ++ (show e)
match _ _ = Left "Unknown error encountered in matching."

unify' :: [(ABT, ABT)] -> Either String [(ABT, ABT)]
-- one cycle of the unification process
unify' [] = Right []
-- Delete / Decompose / Conflict
unify' ((Var v1, Var v2) : eqs) | v1 /= v2  = Left $ "Variable mismatch : " ++ (show v1) ++ " and " ++ (show v2)
                                | otherwise = Right eqs
unify' ((Bind e1, Bind e2) : eqs) = Right ((e1, e2) : eqs)
unify' ((Node n args, Node n' args') : eqs)
    | n /= n'                     = Left $ "Node name mismatch : " ++ n ++ " and " ++ n'
    | length args /= length args' = Left $ "Node arity mismatch : " ++ n ++ " and " ++ n'
    | otherwise = Right ((zip args args') ++ eqs)
-- Swap
unify' ((v@(Var _),    m@(MetaVar _ (Shift 0))) : eqs) = Right ((m, v) : eqs)
unify' ((n@(Node _ _), m@(MetaVar _ (Shift 0))) : eqs) = Right ((m, n) : eqs)
unify' ((b@(Bind _),   m@(MetaVar _ (Shift 0))) : eqs) = Right ((m, b) : eqs)
-- Eliminate / Check
unify' ((m@(MetaVar n (Shift 0)), expr) : eqs)
  | m == expr = Right eqs
  | m `elem` (freeMetaVar expr) = Left $ "Occurs check : " ++ show m ++ " ~ " ++ show expr
  | m `notElem` (freeMetaVarEqs eqs) = Right (eqs ++ [(m, expr)])
  | otherwise = Right ((m, expr) : (substituteEqs eqs [(n, expr)]))
-- The other part of swap : rigid meta-variables
unify' ((m'@(MetaVar _ _), m@(MetaVar _ (Shift 0))) : eqs) = Right ((m, m') : eqs)
unify' ((x, y):eqs) = Right (eqs ++ [(x, y)]) -- postpones this, but we then needs to check for dead-loops


unify :: [(ABT, ABT)] -> Either String Assignment
-- unify equations ~> substitutions
-- TODO this currently sees meta-variables with closures as rigid.
-- we may implement a more powerful unification algorithm that
-- helps implicit argument inference.
unify eqs = do
  d <- done eqs
  if d
    then return (clean eqs)
    else do
      next <- unify' eqs
      result <- unify next
      return result
  where done :: [(ABT, ABT)] -> Either String Bool
        done [] = Right True
        done eqs | all helper' eqs && not ((map fst eqs) `occurs` (map snd eqs)) = Right True
                 | not (all dead eqs) = Right False
                 | otherwise = error $ "The algorithm gives up on equations " ++ show eqs

        helper' :: (ABT, ABT) -> Bool
        helper' (MetaVar n (Shift 0), expr) = True
        helper' _ = False

        occurs :: [ABT] -> [ABT] -> Bool
        occurs ms exprs = any (`elem` (concatMap freeMetaVar exprs)) (map clean' ms)

        clean' :: ABT -> ABT
        clean' m@(MetaVar _ (Shift 0)) = m
        clean' _ = error "Panic! The algorithm has something wrong!!"

        clean :: [(ABT, ABT)] -> Assignment
        clean = map helper
        
        helper :: (ABT, ABT) -> (MetaName, ABT)
        helper (MetaVar n (Shift 0), expr) = (n, expr)
        helper _ = error "Panic! The algorithm has something wrong!!"

        dead :: (ABT, ABT) -> Bool
        dead (Var _, Var _) = False
        dead (Bind _, Bind _) = False
        dead (Node _ _, Node _ _) = False
        dead (_, MetaVar _ (Shift 0)) = False
        dead (MetaVar _ (Shift 0), _) = True
        dead (x, y) = not (x == y)
