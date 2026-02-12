import Mathlib

example {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b := by
  -- try
  exact (mul_self_le_mul_self_iff ha hb).1 h
