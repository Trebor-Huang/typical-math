module Tests (a,b,f,g,x,y) where

import ABT
import Match
import Utilities
import Bidirectional
import Knowledge

k = Node "λ" [Bind $ Node "λ" [Bind $ Var 1]]

-- e shift 0 == e

a = Node "a" []
b = Node "b" []
f = Node "f"
g = Node "g"
x = justMetaVar "X"
y = justMetaVar "Y"

z = Node "Z" []
s x = Node "suc" [x]

isNat x = Node "isNat" [x]
zNat = Rule [] (isNat z) "zNat"
sNat = Rule [isNat x] (isNat (s x)) "sNat"

sszNat = Derivation sNat 
  [Derivation sNat 
    [Derivation zNat []
      (isNat z)]
    (isNat (s z))]
  (isNat (s (s z)))

Just sszNat_auto = (isNat (s (s z))) `inferWith` [zNat, sNat]
result = checkDerivation sszNat

---------- Test for meta-substitution with closures
expr = substitute x (Shift 2)