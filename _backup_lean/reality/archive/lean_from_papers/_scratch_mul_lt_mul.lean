import Mathlib

example {a b c d : ℝ} (h1 : a < b) (h2 : c < d) (ha : 0 ≤ a) (hc : 0 ≤ c) : a*c < b*d := by
  exact mul_lt_mul'' h1 h2 ha hc
