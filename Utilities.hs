module Utilities
  ( mergeAssoc
  , mergeAssocs
  , substituteEqs
  , freeMetaVarEqs
  , justMetaVar
  , showAssignment
  ) where

import           Control.Monad (guard, foldM)
import           ABT

-- utilities
mergeAssoc :: Assignment -> Assignment -> Maybe Assignment
-- require Alternative m to use `guard` function
mergeAssoc [] assoc = return assoc
mergeAssoc ((k, v):as) assoc = (append (k, v) assoc) >>= mergeAssoc as
  where append :: (MetaName, ABT) -> Assignment -> Maybe Assignment
        append (k, v) assoc =
          case lookup k assoc of
            Just v' -> guard (v == v') >> return assoc
            Nothing -> return $ (k, v) : assoc `substituteSubs` [(k, v)]

mergeAssocs :: [Assignment] -> Maybe Assignment
mergeAssocs asss = foldM mergeAssoc [] asss

substituteEqs :: [(ABT, ABT)] -> Assignment -> [(ABT, ABT)]
substituteEqs eqs subs =
  map (\(e1, e2) -> (metaSubstitute e1 subs, metaSubstitute e2 subs)) eqs

substituteSubs :: Assignment -> Assignment -> Assignment
substituteSubs s subs =
  map (\(m, e2) -> (m, metaSubstitute e2 subs)) s

metaSubstituteCompose = flip substituteSubs

freeMetaVarEqs :: [(ABT, ABT)] -> [ABT]
freeMetaVarEqs = nubMetaVar . concatMap helper
  where helper :: (ABT, ABT) -> [ABT]
        helper (e1, e2) = (freeMetaVar e1) ++ (freeMetaVar e2)

justMetaVar :: String -> ABT
justMetaVar s = MetaVar (Meta s 0) (Shift 0)

showAssignment :: Assignment -> String
showAssignment = concatMap showOne
  where showOne :: (MetaName, ABT) -> String
        showOne (n, e) = show n ++ " & \\leftarrow " ++ show e ++ " \\\\ \n "
