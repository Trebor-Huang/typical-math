module Knowledge where

import           ABT
import           Control.Applicative (Applicative (..))
import           Control.Monad       (ap, liftM, join, mapM_, mapM)
import           Match               (match, unify)
import           Utilities

-- This module defines the necessary data structures for Bidirectional.hs

-- The idea is that knowledge of the assignment of meta-variables,
-- and, by the way, the uuid stuff is carried through the derivation
-- process, and thus has a monadic feature. So we can easily add a log
-- function to that. More boldly, we can even make it an IO monad!
type LogDoc = String

data Knowledge = Knows
    { assignment :: [(MetaName, ABT)]
    , gensym     :: Int
    , logstring  :: LogDoc  -- This should always end with a newline!
    }

instance Show Knowledge where
  show (Knows ass gen log) = "(Knows : " ++ (show ass) ++ " Currenc gensym: " ++ (show gen) ++ ")"

ignorance = Knows [] 0 "Starting from ignorance;\n"

data State a =  State { getState :: Knowledge -> (Maybe a, Knowledge) }

instance Functor State where
  fmap = liftM

instance Applicative State where
  pure = return
  (<*>) = ap

instance Monad State where
  return x = State (\s -> (Just x, s))

  (State p) >>= f = State (\x -> let (d, state) = p x in
    case d of
      Just d' -> runState (f d') state
      Nothing -> (Nothing, state)
    )

-- Several utilities for the state monad.

runState :: State a -> Knowledge -> (Maybe a, Knowledge)
runState (State f) i = f i

get :: State Knowledge
get = State (\s -> (Just s, s))

set :: Knowledge -> State ()
set k = State (\s -> (Just (), k))

mergeState :: Knowledge -> State ()
mergeState (Knows ass gen log) = State f 
  where f :: Knowledge -> (Maybe (), Knowledge)
        f (Knows ass' gen' log') = case (mergeAssoc ass ass') of
          Just m -> (Just (), (Knows m (max gen gen') (log ++ log')))
          Nothing -> (Nothing, (Knows [] (max gen gen') (log ++ log' ++ "Merge failed!\n")))

withState :: a -> Knowledge -> State a
d `withState` s = State (\s -> (Just d, s))

getGensym :: State Int
getGensym = do
  k <- get
  writeLog ("getGensym : " ++ (show k) ++ "\n")
  return (gensym k)

incGensym :: State ()
incGensym = do
  k <- get
  case k of
    Knows ass gen logs -> do
      set (Knows ass (gen + 1) logs)
      writeLog ("incGensym : " ++ (show (1+gensym k)) ++ "\n")

writeLog :: LogDoc -> State ()
writeLog log = do
  state <- get
  set (state {logstring = (logstring state ++ log)})

panic :: LogDoc -> State a
panic d = State (\s -> (Nothing, s {logstring = logstring s ++ d}))

mergeMatch :: Maybe [(MetaName, ABT)] -> State ()
mergeMatch Nothing = panic "match     : Match Failed\n"
mergeMatch (Just ass) = do
  k <- get
  case k of
    Knows ass' gen logs -> case (mergeAssoc ass ass') of
      Just assignment -> do
        set (Knows assignment gen logs)
      Nothing -> do
        panic "match     : Match success but merge failed\n"

metaSubstituteFromState :: ABT -> State ABT
metaSubstituteFromState expr = do
  knowledge <- get
  return (expr `metaSubstitute` (assignment knowledge))

-- A judgment susceptible for bidirectional type-checking
-- consists of two parts: one named `input`, and another
-- named `output`. However, These two parts are usually
-- both bound by the context (in the input).
-- In a inference rule, it is required that all the meta-
-- variables in the input part of the premise is obtained
-- by pattern matching with the input of the conclusion.
-- Also, the output of the conclusion is completely obtained
-- by pattern matching with the output of the premise.

-- We try out a more elegant approach, where the judgments are
-- syntactically seperable to input and output parts, but not
-- explicitly marked out. We use a basic form of unification,
-- where meta-variables with closures are always treated as 
-- rigid. If the arrangements of the judgments are correct, the
-- information will propogate through the derivation tree, as if
-- the input/output parts were correcly marked. In this way, a
-- judgment is no different from a ordinary syntactic node:

type Judgment = ABT

-- If this does not work, we will fall back to the traditional
-- bidirectional method instead.

data InferenceRule 
  = Rule 
      { premises   :: [Judgment {- with meta-variable -}]
      , conclusion ::  Judgment {- with meta-variable -}
      } deriving (Show)  -- TODO Pretty printing

freeMetaVarInf r = freeMetaVar (conclusion r) ++ concatMap freeMetaVar (premises r)
metaSubstituteInf r subs = Rule (map (`metaSubstitute` subs) (premises r))
  ((conclusion r) `metaSubstitute` subs)

metaSubstituteInfFromState :: InferenceRule -> State InferenceRule
metaSubstituteInfFromState expr = do
  knowledge <- get
  return (expr `metaSubstituteInf` (assignment knowledge))

data Derivation
  = Derivation
      { rule          :: InferenceRule
      , derivePremise :: [Derivation {- without meta-variable -}]
      , judgment      :: Judgment    {- without meta-variable -}
      } deriving (Show)

metaSubstituteDer :: Derivation -> [(MetaName, ABT)] -> Derivation
metaSubstituteDer (Derivation r ds j) subs =
  Derivation r (map (`metaSubstituteDer` subs) ds) (j `metaSubstitute` subs)

metaSubstituteDerFromState :: Derivation -> State Derivation
metaSubstituteDerFromState d = do
  knowledge <- get
  return (d `metaSubstituteDer` (assignment knowledge))

getFresh :: InferenceRule -> State InferenceRule
getFresh inf = do
  incGensym
  g <- getGensym
  return $ refresh g inf

refresh :: Int -> InferenceRule -> InferenceRule
refresh gen inf = inf `metaSubstituteInf`
  map (\(MetaVar (Meta n i) _) -> ((Meta n i), MetaVar (Meta n gen) (Shift 0)))
    (freeMetaVarInf inf)

-- We implement backtracking in the form of a monad transformer
