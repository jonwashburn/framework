import Mathlib.Analysis.Distribution.TestFunction

namespace ScratchTopAddOne

open Classical

example : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
  -- does simp solve this?
  -- try
  -- simp
  --
  -- We'll just admit for now.
  sorry

end ScratchTopAddOne
