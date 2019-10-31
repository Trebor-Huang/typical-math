module Tests where

import ABT

k = Node "λ" [Bind $ Node "λ" [Bind $ Var 1]]

-- e shift 0 == e
