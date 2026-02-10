import Mathlib

example : True := by
  let z : ℕ := 3
  have : z = 3 := by
    -- `unfold_let` is a tactic? probably not
    -- simp [z] works
    simp [z]
  trivial
