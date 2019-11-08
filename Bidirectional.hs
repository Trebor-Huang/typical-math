module Bidirectional where

import ABT

judgement :: String -> ABT -> ABT -> ABT  -- bidirectional judgment
judgment name inn outn  = Node name [inn, outn]

data Knowledge = (MetaVariable-Assignment, Log, DerivationTree)
