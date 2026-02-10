import Mathlib

example {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : a^2 < b^2 := by
  have h := pow_lt_pow_left₀ hab ha (n := 2) (by decide : (2:ℕ) ≠ 0)
  simpa using h
