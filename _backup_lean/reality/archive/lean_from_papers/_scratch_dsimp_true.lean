import Mathlib
example : True := by
  dsimp
  -- if dsimp didn't close, there would still be a goal here
  trivial
