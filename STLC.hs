-- Tests the Bidirectional.hs system with STLC
module STLC where

import ABT
import Utilities
import Bidirectional

[x, y, g, a, b, m, n] = map justMetaVar ["x", "y", "Γ", "A", "B", "M", "N"]

empty = Node "emptyctx" []
-- \newcommand{\emptyctx}{*}
cons ts x t = Node "consctx" [ts, x, t]
-- \newcommand{\consctx}[3]{#1 , #2 {:} #3}

variable = Node "star" [] -- no need for newcommand
apostrophe x = Node "apostr" [x]
-- \newcommand{\apostr}[1] {#1'}

ctx g = Node "ctx" [g]
-- \newcommand{\ctx}[1]{#1 \ \mathsf{ctx}}
tp t = Node "type" [t]
-- \newcommand{\type}[1]{#1 \ \mathsf{type}}

emptyCtx = Rule [] (ctx empty) "Ctx-Empty"
consCtx  = Rule [ctx g, tp a, isfresh g x] (ctx (cons g x a)) "Ctx-Cons"

lkup  g v t = Node "lookup" [g, v, t]
-- \newcommand{\lookup}[3]{#1 \vdash #2 \mathbf{lookup} \rightsquigarrow #3}
lookupStop = Rule [ctx (cons g x a)] (lkup (cons g x a) x a) "Lookup-Stop"
lookupPop  = Rule [lkup g y b] (lkup (cons g x a) y b) "Lookup-Pop"

synth g e t = Node "synth"  [g, e, t]
-- \newcommand{\synth}[3]{#1 \vdash #2 \mathbf{synth} \rightsquigarrow #3}
check g e t = Node "checkj"  [g, e, t]
-- \newcommand{\checkj}[3]{#1 \vdash \mathbf{check} #2 : #3}
fresh g v x = Node "fresh"  [g, v, x]
-- \newcommand{\fresh}[3]{#1 \vdash #2 \mathbf{fresh} \rightsquigarrow #3}
justFresh = Rule [isfresh g x] (fresh g x x) "JustFresh"
reFresh   = Rule [fresh g (apostrophe x) y] (fresh g x y) "Refresh"

isfresh g v = Node "isfresh" [g, v]
-- \newcommand{\isfresh}[2]{#1 \vdash #2 \mathbf{fresh}}
emptyFresh = Rule [] (isfresh empty x) "Empty-Fresh"
consFresh  = Rule [isfresh g x, differs x y] (isfresh (cons g y b) x) "Cons-Fresh"

differs x y = Node "differs" [x, y]
-- \newcommand{\differs}[2]{#1 \# #2}
differsSL = Rule [] (differs variable (apostrophe x)) "Differ-Left"
differsSR = Rule [] (differs (apostrophe x) variable) "Differ-Right"
differsS  = Rule [differs x y] (differs (apostrophe x) (apostrophe y)) "Differ-Step"

lam t e = Node "lambda" [t, Bind e]  -- no new command needed
app e f = Node "application" [e, f]
-- \newcommand{\application}[2]{(#1\ #2)}

true = Node "true" []
-- \newcommand{\true}{\mathrm{T}}
false = Node "false" []
-- \newcommand{\false}{\mathrm{F}}
sole = Node "sole" []
-- \newcommand{\sole}{\mathrm{i}}

to a b = Node "To" [a, b]
-- \newcommand{\To}[2]{#1 \to #2}
bool = Node "Bool" []
-- \newcommand{\Bool}{\mathbb{B}}
one = Node "One" []
-- \newcommand{\One}{\mathbf 1}
boolType = Rule [] (tp bool) "Bool-Form"
oneType  = Rule [] (tp one)  "One-Form"
toType   = Rule [tp a, tp b] (tp (a `to` b)) "To-Form"

rules = [emptyCtx, consCtx, lookupPop, lookupStop, justFresh, reFresh, emptyFresh, consFresh,
  differsS, differsSL, differsSR, boolType, oneType, toType]

differ1 = (differs (apostrophe $ apostrophe variable) (apostrophe variable)) `inferWithLog` rules
