-- Tests the Bidirectional.hs system with STLC
module STLC where

import ABT
import Utilities
import Bidirectional

[x, y, g, a, b, m, n] = map justMetaVar ["x", "y", "Γ", "A", "B", "M", "N"]

empty = Node "*" []
cons t ts = Node "," [t, ts]

ctx g = Node "ctx" [g]
tp t = Node "type" [t]
lkup  g v t = Node "lookup" [g, v, t]
synth g e t = Node "synth"  [g, e, t]
check g e t = Node "check"  [g, e, t]

lam t e = Node "λ" [t, Bind e]
app e f = Node "@" [e, f]

true = Node "T" []
false = Node "F" []
sole = Node "()" []

to a b = Node "->" [a, b]
bool = Node "Bool" []
one = Node "1" []

emptyContext = Rule [] 
            -------------
              (ctx empty)
consContext  = Rule [tp a, ctx g]
              --------------------
                (ctx (cons a g))

