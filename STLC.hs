-- Tests the Bidirectional.hs system with STLC
module STLC where

import ABT
import Utilities
import Bidirectional

[x, y, g, a, b, c, m, n, e, f, t] = map justMetaVar ["x", "y", "\\Gamma", "A", "B", "C", "M", "N", "e", "f", "t"]

{-
\newcommand{\emptyctx}{*}
\newcommand{\consctx}[2]{{#1 , #2}}
\newcommand{\apostr}[1] {{#1'}}
\newcommand{\ctx}[1]{#1 \ \mathsf{ctx}}
\newcommand{\type}[1]{#1 \ \mathsf{type}}
\newcommand{\var}[1]{#1 \ \mathsf{var}}
\newcommand{\lookup}[3]{#1 \vdash\, #2 \mathbf{lookup} \rightsquigarrow #3}
\newcommand{\synth}[3]{#1 \vdash\, #2 \mathbf{synth} \rightsquigarrow #3}
\newcommand{\checkj}[3]{#1 \vdash \mathbf{check}\, #2 : #3}
\newcommand{\normalizes}[4]{#1 \vdash\, #2 \rightsquigarrow_\beta^{#3} #4}
\newcommand{\fresh}[2]{#1 \vdash \mathbf{fresh} \rightsquigarrow #2}
\newcommand{\abstraction}[2]{(\lambda^{#1} #2)}
\newcommand{\application}[2]{(#1\ #2)}
\newcommand{\true}{\mathrm{T}}
\newcommand{\false}{\mathrm{F}}
\newcommand{\sole}{\mathrm{i}}
\newcommand{\To}[2]{(#1 \to #2)}
\newcommand{\Bool}{\mathbb{B}}
\newcommand{\One}{\mathbf{1}}
\newcommand{\ifthenelse}[3]{(\texttt{if } #1 \texttt{ then } #2 \texttt{ else } #3)}
\newcommand{\zero}{\mathrm{O}}
\newcommand{\successor}[1]{\mathrm{succ}(#1)}
\newcommand{\primrec}[3]{\mathrm{rec}_{\mathbb N}(#1, #2, #3)}
\newcommand{\nat}{\mathbb N}
\newcommand{\SingleBeta}[3]{#1\ #2 \rightsquigarrow_{\beta} #2}
-}

empty = Node "emptyctx" []
cons ts t = Node "consctx" [ts, t]

variable = Node "star" [] -- no need for newcommand
apostrophe x = Node "apostr" [x]

ctx g = Node "ctx" [g]
tp t = Node "type" [t]
var t = Node "var" [t]

varVar = Rule [] (var variable) "Var-Var"
varApo = Rule [var x] (var (apostrophe x)) "Var-Apo"

emptyCtx = Rule [] (ctx empty) "Ctx-Empty"
consCtx  = Rule [ctx g, tp a] (ctx (cons g a)) "Ctx-Cons"

lkup  g v t = Node "lookup" [g, v, t]
lookupStop = Rule [ctx (cons g a), fresh g x] (lkup (cons g a) x a) "Lookup-Stop"
lookupPop  = Rule [lkup g y b] (lkup (cons g a) y b) "Lookup-Pop"

synth g e t = Node "synth"  [g, e, t]
check g e t = Node "checkj"  [g, e, t]
varSynth = Rule [lkup g x a] (synth g x a) "Var-Synth"
varCheck = Rule [lkup g x a] (check g x a) "Var-Check"
appSynth = Rule [synth g n b, check g m (to b a)] (synth g (app m n) a) "App-Synth"
appCheck = Rule [synth g m (to b a), check g n b] (check g (app m n) a) "App-Check"
absSynth = Rule [fresh g x, synth (cons g a) (beta (Bind m) x) b]
                    (synth g (lam a m) (to a b)) "Abs-Synth"
absCheck = Rule [fresh g x, check (cons g a) (beta (Bind m) x) b]
                    (check g (lam a m) (to a b)) "Abs-Check"
ifSynth = Rule [check g b bool, synth g m a, check g n a]
  (synth g (ifthenelse b m n) a) "If-Synth"
ifCheck = Rule [check g b bool, check g m a, check g n a]
  (check g (ifthenelse b m n) a) "If-Check"
zSynth = Rule [ctx g] (synth g zro nat) "Zero-Synth"
sSynth = Rule [ctx g, check g n nat] (synth g (suc n) nat) "Succ-Synth"
primSynth = Rule [synth g n a,
  check g e a,
  check g f (to a a)] (synth g (primrec e f n) a) "Rec-Synth"
normalize g e t n = Node "normalizes" [g, e, t, n]
normVar = Rule [lkup g x a] (normalize g x a x) "Beta-Var"
normLam = Rule [fresh g x,
  normalize g (beta (Bind e) x) b f]
  (normalize g (lam a e) (to a b) (lam a f)) "Beta-Lam"
normBeta = Rule [synth g f a,
    normalize g e (to a b) (lam a m),
    normalize g f a n,
    normalize g (beta (Bind m) n) b y
  ] (normalize g (app e f) b y) "Beta"
normApp = Rule [synth g f a,
    normalize g e (to a b) m,
    normalize g f a n] (normalize g (app e f) b (app m n)) "Beta-App"
normIfTrue = Rule [
  normalize g b bool true,
  check g m a,
  check g n a,
  normalize g m a e] (normalize g (ifthenelse b m n) a e) "If-True"
normIfFalse = Rule [
  normalize g b bool false,
  check g m a,
  check g n a,
  normalize g n a e] (normalize g (ifthenelse b m n) a e) "If-False"
normSucc = Rule [
    normalize g n nat m
  ] (normalize g (suc n) nat (suc m)) "Beta-Succ"
normZPrim = Rule [check g e a, check g f (to a a), normalize g e a b]
  (normalize g (primrec e f zro) a b) "PrimRec-Zero"
normSPrim = Rule [normalize g (primrec e f n) a m,
  normalize g (app f m) a b]
  (normalize g (primrec e f (suc n)) a b) "PrimRec-Succ"

fresh g x = Node "fresh"  [g, x]
justFresh = Rule [] (fresh empty variable) "JustFresh"
reFresh   = Rule [tp a, fresh g x] (fresh (cons g a) (apostrophe x)) "Refresh"

lam t e = lam' t (Bind e)
lam' t e = Node "abstraction" [t, e]
app e f = Node "application" [e, f]
ifthenelse a b c = Node "ifthenelse" [a, b, c]

singleBeta f a e = Node "SingleBeta" [f, a, e]
sBAux = Rule [] (singleBeta (Bind f) a (beta (Bind f) a)) "Beta-Aux"

true = Node "true" []
trueBool = Rule [ctx g] (synth g true bool) "True-Bool"
false = Node "false" []
falseBool = Rule [ctx g] (synth g false bool) "False-Bool"
sole = Node "sole" []
soleOne = Rule [ctx g] (synth g sole one) "Sole-One"
checkSynth = Rule [synth g a b] (check g a b) "Switch"

zro = Node "zero" []
suc n = Node "successor" [n]

primrec z s i = Node "primrec" [z, s, i]

normal = Rule [check g e a] (normalize g e a e) "Normal"

to a b = Node "To" [a, b]
bool = Node "Bool" []
one = Node "One" []
nat = Node "nat" []
boolType = Rule [] (tp bool) "Bool-Form"
oneType  = Rule [] (tp one)  "One-Form"
toType   = Rule [tp a, tp b] (tp (a `to` b)) "To-Form"
natType  = Rule [] (tp nat) "Nat-Form"

rules = [justFresh, reFresh,
  emptyCtx, consCtx,
  lookupStop, lookupPop,
  boolType, oneType, toType, natType,
  varVar, varApo,
  varCheck, varSynth, appCheck, appSynth, absCheck, absSynth, checkSynth,
  ifCheck, ifSynth, zSynth, sSynth, primSynth,
  trueBool, falseBool, soleOne,
  sBAux, normVar, normLam, normBeta, normApp,
  normIfTrue, normIfFalse,
  normSucc, normZPrim, normSPrim,
  normal]

test2 = (ctx (cons 
      (cons empty (to one one))
      (to (to bool one) bool)
    )
  ) `inferWith` rules
test3 = 
  (lkup 
    (cons
      (cons
        (cons empty bool)
        one)
      (to (to bool bool) bool))
    (apostrophe variable)
    a) `inferWith` rules  -- this is looking like lisp??!
test4 =
  (synth
    empty
    (lam bool (Var 0))
    a) `inferWith` rules
test5 =
  (synth
    empty
    (lam (to one (to bool bool)) 
      (lam (to one bool) 
        (lam one 
          (app
            (app (Var 2) (Var 0))
            (app (Var 1) (Var 0))  -- \x -> \y -> \z -> (x z) (y z)
          ))))
    a) `inferWith` rules

test6 = (normalize empty (app (lam bool (Var 0)) true) bool e) `inferWith` rules
test7 = (normalize empty
  (ifthenelse
    (app
      (lam bool (ifthenelse
        (Var 0)
        false
        true))
      false)
    true
    false)
  bool e) `inferWith` rules

test8 = (normalize empty 
  (app 
    (app
      (lam nat -- x
        (lam nat -- y
          (primrec
            (Var 0)
            (lam nat (suc (Var 0))) -- eta-long form of suc
            (Var 1)
          )
        )
      )
    (suc $ suc $ suc zro))
  (suc zro))
  nat e) `inferWith` rules
