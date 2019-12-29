module Utilities
  ( mergeAssoc
  , mergeAssocs
  , substituteEqs
  , freeMetaVarEqs
  , justMetaVar
  , showAssignment
  ) where

import           Control.Monad (foldM, join, liftM2, mapM, liftM)
import           ABT

-- utilities
mergeAssoc :: Assignment -> Assignment -> Maybe Assignment
mergeAssoc [] assoc = Just assoc
mergeAssoc ((k, v):as) assoc =
  (append (k, v) assoc) >>= (\assoc' -> mergeAssoc as assoc')
  where
    append :: (MetaName, ABT) -> Assignment -> Maybe Assignment
    append (k, v) assoc
      | k `elem` (map fst assoc) =
        case v == snd (head (filter ((== k) . fst) assoc)) of
          True  -> Just assoc
          False -> Nothing
      | otherwise = Just ((k, v) : assoc `substituteSubs` [(k, v)])

mergeAssocs :: [Assignment] -> Maybe Assignment
mergeAssocs asss = join $ foldM (liftM2 mergeAssoc) (Just []) (map Just asss)

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
        helper (e1, e2) = nubMetaVar $ (freeMetaVar e1) ++ (freeMetaVar e2)

justMetaVar :: String -> ABT
justMetaVar s = MetaVar (Meta s 0) (Shift 0)

showAssignment :: Assignment -> String
showAssignment = concatMap showOne
  where showOne :: (MetaName, ABT) -> String
        showOne (n, e) = show n ++ " & \\leftarrow " ++ show e ++ " \\\\ \n "
