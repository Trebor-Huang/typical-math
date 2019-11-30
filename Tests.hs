module Tests(a,b,f,g,x,y) where

import ABT
import Match
import Utilities
import Bidirectional

k = Node "λ" [Bind $ Node "λ" [Bind $ Var 1]]

-- e shift 0 == e

a = Node "a" []
b = Node "b" []
f = Node "f"
g = Node "g"
x = justMetaVar "X"
y = justMetaVar "Y"

z = Node "Z" []
s x = Node "S" [x]

isNat x = Node "isNat" [x]
zNat = Rule [] (isNat z)
sNat = Rule [isNat x] (isNat (s x))

sszNat = Derivation sNat 
  [Derivation sNat 
    [Derivation zNat []
      (isNat z)]
    (isNat (s z))]
  (isNat (s (s z)))

sszNat_auto = (isNat (s (s z))) `inferWith` [zNat, sNat]
result = checkDerivation sszNat

