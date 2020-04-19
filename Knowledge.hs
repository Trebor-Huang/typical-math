{-# LANGUAGE MultiParamTypeClasses, TupleSections #-}
module Knowledge
  ( LogDoc
  , Knowledge(..)
  , ignorance
  , State(..)
  , get
  , put
  , getAssignment
  , getGensym
  , getFresh
  , writeLog
  , panic
  , mergeMatch
  , Judgment(..)
  , Derivation(..)
  , InferenceRule(..)
  , metaSubstituteFromState
  , metaSubstituteDer
  , metaSubstituteDerFromState
  , metaSubstituteInf
  , metaSubstituteInfFromState
  , StateBacktrack(..)
  , liftBacktrack
  , caseSplit
  ) where

import           ABT
import           Control.Applicative (Applicative (..))
import           Control.Monad       (ap, liftM, join, mapM_, mapM)
import           Control.Monad.State (MonadState (..), gets, modify)
import           Data.List           (intercalate)
import           Match               (match, unify)
import           Utilities

-- This module defines the necessary data structures for Bidirectional.hs
-- The idea is that knowledge of the assignment of meta-variables,
-- and, by the way, the uuid stuff is carried through the derivation
-- process, and thus has a monadic feature. So we can easily add a log
-- function to that. More boldly, we can even make it an IO monad!
type LogDoc = String

data Knowledge = Knows
    { assignment :: Assignment
    , gensym     :: Int
    , logstring  :: LogDoc
    }

instance Show Knowledge where
  show (Knows a g l) = "\\boxed{\n \\begin{aligned}\n "
    ++ " & \\textrm{Current Gensym is " ++ show g ++ "} \\\\ \n"
    ++ "\\\\ \n" ++ concatMap ((" & \\textrm{" ++) . (++ "} \\\\ \n")) (lines l)
    ++ "\\end{aligned}\n}"

ignorance = Knows [] 0 "Starting from ignorance;\n"

newtype State a = State { runState :: Knowledge -> (Maybe a, Knowledge) }

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

instance MonadState Knowledge State where
  get = State (\s -> (Just s, s))
  put k = State (\s -> (Just (), k))
  state f = State (\s -> let (a, s') = f s in (Just a, s'))

-- Several utilities for the state monad.

getAssignment :: State Assignment
getAssignment = gets assignment

setAssignment :: Assignment -> State ()
setAssignment ass = modify (\x -> x { assignment = ass })

getGensym :: State Int
getGensym = gets gensym

setGensym :: Int -> State ()
setGensym ass = modify (\x -> x { gensym = ass })

incGensym :: State ()
incGensym = modify (\x -> x { gensym = gensym x + 1 })

writeLog :: LogDoc -> State ()
writeLog log = modify (\s -> s { logstring = (logstring s ++ log) })

panic :: LogDoc -> State a
panic d = State (\s -> (Nothing, s {logstring = logstring s ++ d}))

mergeMatch :: Either String Assignment -> State ()
mergeMatch (Left s) = panic (s ++ "\n")
mergeMatch (Right ass) = do
  k <- get
  case (mergeAssoc ass (assignment k)) of
    Just assignment -> put (k {assignment = assignment})
    Nothing -> panic "Match success but merge failed\n"

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
      , name :: String
      }

instance Show InferenceRule where
  show (Rule prems concl name) = "\\frac{\\displaystyle{" ++
    intercalate "\\quad " (map show prems)
    ++ "}}{\\displaystyle{" ++
    show concl
    ++ "}}" ++ "\\textsc{\\tiny " ++ name ++ "}"


freeMetaVarInf r = nubMetaVar $ concatMap freeMetaVar (conclusion r : premises r)
metaSubstituteInf r subs = Rule (map (`metaSubstitute` subs) (premises r))
  ((conclusion r) `metaSubstitute` subs) (name r)

metaSubstituteInfFromState :: InferenceRule -> State InferenceRule
metaSubstituteInfFromState expr = do
  knowledge <- get
  return (expr `metaSubstituteInf` (assignment knowledge))

data Derivation
  = Derivation
      { rule          :: InferenceRule
      , derivePremise :: [Derivation {- without meta-variable -}]
      , judgment      :: Judgment    {- without meta-variable -}
      }

instance Show Derivation where
  show (Derivation rule prem judg) = "{\n\\frac{\\displaystyle{" ++ intercalate "\\quad " (map show prem) ++ "}}\n{" ++
    (show judg) ++ "}" ++ ("\\vphantom{ " ++ name rule ++ "}") ++ "\n}"  -- change \vphantom to \textsc{\tiny} if needed

metaSubstituteDer :: Derivation -> Assignment -> Derivation
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
  -- writeLog $ "Current gensym: " ++ show g ++ "\n"
  -- writeLog $ "The variables to be substituted: $" ++ show (freeMetaVarInf inf) ++ "$\n"
  return $ refresh g inf

refresh :: Int -> InferenceRule -> InferenceRule
refresh gen inf = inf `metaSubstituteInf`
  map (\(MetaVar (Meta n i) s) -> ((Meta n i), MetaVar (Meta n gen) s))
    (freeMetaVarInf inf)

-- Actually there is no backtracking happening here
-- We store all the failures with a Nothing

-- TODO: we need to enhance the log structure in backtracking
-- TODO: for instance, we can do interactive stuff
-- TODO: we can generalize these monads

newtype StateBacktrack a =  StateBacktrack { runStateBacktrack :: Knowledge -> [(Maybe a, Knowledge)] }

instance Functor StateBacktrack where
  fmap = liftM

instance Applicative StateBacktrack where
  pure = return
  (<*>) = ap

instance Monad StateBacktrack where
  return x = StateBacktrack $ pure . (Just x,)

  (StateBacktrack p) >>= f = StateBacktrack (\s ->
      [ b | a <- p s, b <- case fst a of
          Nothing -> [(Nothing, snd a)]
          Just ar -> runStateBacktrack (f $ ar) (snd a)
        ]
    )

liftBacktrack :: State a -> StateBacktrack a
liftBacktrack (State f) = StateBacktrack (pure . f)

caseSplit :: [a] -> StateBacktrack a
caseSplit cases = StateBacktrack (\s -> [(Just c, s) | c <- cases])
