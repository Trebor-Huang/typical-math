module ABT
  ( VarName
  , NodeType
  , ABT(..)
  , Substitution
  , compose
  , substitute
  , beta
  , metaSubstitute
  ) where

type VarName = Int

type NodeType = String

data ABT
  = Var VarName
  | Node NodeType [ABT]
  | Bind ABT
  | MetaVar String Substitution
  deriving (Eq)

-- Uses De Bruijn Indices starting from zero; therefore we can just derive the Eq class
-- TODO See if the String param in Node should be replaced with a record type of Node types
-- TODO Pretty print
instance Show ABT where
  show (Var n)          = show n
  show (Node name abts) = '(' : name ++ concatMap ((' ' :) . show) abts ++ ")"
  show (Bind e)         = '.' : show e
  show (MetaVar s c)    = '?' : s ++ '[' : show c ++ "]"

data Substitution
  = Shift Int
  | Dot ABT Substitution
  deriving (Eq)

instance Show Substitution where
  show (Shift k) = '^' : show k
  show (Dot e s) = show e ++ " . " ++ show s

compose :: Substitution -> Substitution -> Substitution
compose s (Shift 0)         = s
compose (Dot _ s) (Shift k) = compose s (Shift (k - 1))
compose (Shift m) (Shift n) = Shift (m + n)
compose s (Dot e t)         = Dot (substitute e s) (compose s t)

substitute :: ABT -> Substitution -> ABT
substitute (Var m) (Shift k) = Var (k + m)
substitute (Var 0) (Dot e _) = e
substitute (Var k) (Dot _ s) = substitute (Var (k - 1)) s
substitute (Bind e) s = Bind (substitute e (Dot (Var 0) (compose (Shift 1) s)))
substitute (Node name abts) s = Node name (map (`substitute` s) abts)
substitute (MetaVar n c) s = MetaVar n (compose s c)

-- We seriously need to check if there is any bug
beta :: ABT -> ABT -> ABT
-- aux function for Bind's beta reduction
beta (Bind e1) e2 = substitute e1 (Dot e2 (Shift 0))
beta _ _          = error "beta is for Bind only."

-- data ABT = Var VarName | Node NodeType [ABT] | Bind ABT | MetaVar String Substitution deriving (Eq)
metaSubstitute :: ABT -> [(String, ABT)] -> ABT
metaSubstitute p [] = p
metaSubstitute m@(MetaVar n s) ((n', e):_)
  | n == n' = substitute e s
  | otherwise = m
metaSubstitute v@(Var _) _ = v
metaSubstitute (Node nt abts) msubs =
  Node nt (map (`metaSubstitute` msubs) abts)
metaSubstitute (Bind abt) msubs = Bind (metaSubstitute abt msubs)
