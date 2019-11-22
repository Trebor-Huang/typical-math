module Tests(a,b,f,g,x,y) where

import ABT
import Match
import Utilities

k = Node "λ" [Bind $ Node "λ" [Bind $ Var 1]]

-- e shift 0 == e

a = Node "a" []
b = Node "b" []
f = Node "f"
g = Node "g"
x = justMetaVar "X"
y = justMetaVar "Y"


