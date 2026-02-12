import Mathlib

example {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : a^2 < b^2 := by
  exact pow_lt_pow_left₀ ha hab 2
