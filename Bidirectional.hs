module Bidirectional
  ( Knowledge(..)
  , Judgment
  , InferenceRule(..)
  , Derivation(..)
  , checkDerivation
  , inferWith
  , State (..)
  , ignorance
  , runState
  ) where

import           ABT
import           Control.Applicative (Applicative (..))
import           Control.Monad       (ap, liftM, liftM2, join, mapM_)
import           Match               (match, unify)
import           Utilities

-- The idea is that knowledge of the assignment of meta-variables,
-- and, by the way, the uuid stuff is carried through the derivation
-- process, and thus has a monadic feature. So we can easily add a log
-- function to that. More boldly, we can even make it an IO monad!
type LogDoc = String

data Knowledge
  = Knows
      { assignment :: [(MetaName, ABT)]
      , gensym     :: Int
      , logstring  :: LogDoc  -- This should always end with a newline!
      }
    | Panic 
      {
        logstring :: LogDoc
      }

instance Show Knowledge where
  show (Knows ass gen log) = "(Knows : " ++ (show ass) ++ " Currenc gensym: " ++ (show gen) ++ ")"
  show (Panic log) = "Panicking!"

ignorance = Knows [] 0 "Starting from ignorance;\n"

data State a = State {_state :: Knowledge -> (a, Knowledge)}

instance Functor State where
  fmap = liftM

instance Applicative State where
  pure = return
  (<*>) = ap

instance Monad State where
  return x = State (\s -> (x, s))

  (State p) >>= f = State (\x -> let (d, state) = p x in runState (f d) state)

-- Several utilities for the state monad.
-- TODO: We cancelled automatic merge in the state monad.

get :: State Knowledge
get = State (\s -> (s, s))

set :: Knowledge -> State ()
set k = State (\s -> ((), k))

withState :: a -> Knowledge -> State a
d `withState` s = State (\s -> (d, s))

runState :: State a -> Knowledge -> (a, Knowledge)
runState (State f) i = f i

getGensym :: State Int
getGensym = do
  k <- get
  writeLog ("getGensym : " ++ (show k) ++ ";\n")
  return (gensym k)

incGensym :: State ()
incGensym = do
  k <- get
  case k of
    Knows ass gen logs -> do
      set (Knows ass (gen + 1) logs)
      writeLog ("incGensym : " ++ (show (1+gensym k)) ++ ";\n")

writeLog :: LogDoc -> State ()
writeLog log = do
  state <- get
  case state of
    Knows ass gen logs -> set (Knows ass gen (logs ++ log))
    Panic logs -> set (Panic (logs ++ log))

panic :: LogDoc -> State ()
panic s = do
  state <- get
  set (Panic ((logstring state) ++ s))

mergeMatch :: Maybe [(MetaName, ABT)] -> State ()
mergeMatch Nothing = panic "[   Match] Match Failed;\n"
mergeMatch (Just ass) = do
  k <- get
  case k of
    Panic logs -> panic logs
    Knows ass' gen logs -> case (mergeAssoc ass ass') of
      Just assignment -> do
        set (Knows assignment gen logs)
        writeLog "[   Match] Match success;\n"
      Nothing -> do
        panic "[   Match] Match success but merge failed;\n"

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

getFresh :: InferenceRule -> State InferenceRule
getFresh inf = do
  g <- getGensym
  incGensym
  return $ refresh (g+1) inf

refresh :: Int -> InferenceRule -> InferenceRule
refresh gen inf = inf `metaSubstituteInf`
  map (\(MetaVar (Meta n i) _) -> ((Meta n i), MetaVar (Meta n gen) (Shift 0)))
    (freeMetaVarInf inf)

checkDerivation :: State Derivation -> State ()
-- checks if the derivation is valid
checkDerivation d = do
  derivation <- d
  -- we first match the rule's conclusion
  useRule <- getFresh (rule derivation)
  mergeMatch (match (judgment derivation) (conclusion useRule))
  -- then we check the premises one by one
  if length (premises useRule) /= length (derivePremise derivation) then
    panic "[   check] The number of premises of a derivation is wrong;"
  else do
    -- first we need to ensure that the premises are in the correct form
    -- as asserted by the `useRule`
    mapM_ (mergeMatch . (uncurry match))
      (zip (map judgment (derivePremise derivation)) (premises useRule))
      -- next we check the premises' derivation, recursively
    currentState <- get
    mapM_ (checkDerivation . (`withState` currentState)) (derivePremise derivation)


inferWith :: Judgment -> InferenceRule -> Maybe Derivation
-- turns a judgment into a derivation, given an inference rule
inferWith = undefined

