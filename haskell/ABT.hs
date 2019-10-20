module ABT where

data ABT = Var Int | FVar String | Node String [ABT] | Bind ABT deriving (Eq)
-- Uses De Bruijn Indices
-- !Starting from 0

instance Show ABT where  -- TODO Pretty print
 show (Var n)           = show n
 show (FVar s)          = s
 show (Node name abts)  = '(' : name ++ foldl (++) "" (map ((' ':) . show) abts) ++ ")"
 show (Bind e)          = '.' : show e

bind :: String -> ABT -> ABT
bind s e = Bind (substitute (e `shift` 1) ([], [(s, Var 0)]))

shift :: ABT -> Int -> ABT
shift (Var n)           k   = Var (n+k)
shift f@(FVar s)        k   = f
shift (Node name abts)  k   = Node name (map (`shift` k) abts)
shift (Bind e)          k   = Bind (substitute e (Var 0 : map Var [(k+1)..], []))

substitute :: ABT -> ([ABT], [(String, ABT)])  -> ABT
-- Substitution is a (potentially infinite) list of substitutions; with free variable substitutions
-- One for each de Bruijn index

substitute v@(Var n)        (subs, fsubs)    = if length subs > n then subs !! n else v
substitute (Node name abts) (subs, fsubs)    = Node name (map (`substitute` (subs, fsubs)) abts)
substitute (Bind e)         (subs, fsubs)    = Bind (substitute e (((Var 0) : (map (`shift` 1) subs)), fsubs))
substitute f@(FVar s)       (subs, fsubs)    = case (lookup s fsubs) of
                                                Just expr   -> expr
                                                Nothing     -> f
-- We seriously need to check if there is any bug

beta :: ABT -> ABT -> ABT
-- aux function for Bind's beta reduction
beta (Bind e1) e2   = substitute e1 ([e2], [])
beta _         _    = error "beta is for Bind only."
