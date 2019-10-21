module ABT where

type VarName = Int
data ABT = Var VarName | Node String [ABT] | Bind ABT | MetaVar String Substitution deriving (Eq)
-- Uses De Bruijn Indices
-- !Starting from 0

instance Show ABT where  -- TODO Pretty print
    show (Var n)           = show n
    show (Node name abts)  = '(' : name ++ foldl (++) "" (map ((' ':) . show) abts) ++ ")"
    show (Bind e)          = '.' : show e
    show (MetaVar s c)     = '%' : show s ++ show c

data Substitution = Shift Int | Dot ABT Substitution

instance Show Substitution where
    show (Shift k)      = '^' : show k
    show (Dot e s)      = show e ++ " . " ++ show s

compose :: Substitution -> Substitution -> Substitution
compose s           (Shift 0) = s
compose (Dot e s)   (Shift k) = compose s (Shift (k-1))
compose (Shift m)   (Shift n) = Shift (m+n)
compose s           (Dot e t) = Dot (substitute e s) (compose s t)

substitute :: ABT -> Substitution -> ABT

substitute (Var m)  (Shift k) = Var (k+m)
substitute (Var 0)  (Dot e s) = e
substitute (Var k)  (Dot e s) = substitute (Var (k-1)) s
substitute (Bind e) s         = Bind (substitute e (Dot (Var 0) (compose (Shift 1) s)))
substitute (Node name abts) s = Node name (map (`substitute` s) abts)
substitute (MetaVar n c)    s = MetaVar n (compose s c)

-- We seriously need to check if there is any bug

beta :: ABT -> ABT -> ABT
-- aux function for Bind's beta reduction
beta (Bind e1) e2   = substitute e1 ([e2], [])
beta _         _    = error "beta is for Bind only."
