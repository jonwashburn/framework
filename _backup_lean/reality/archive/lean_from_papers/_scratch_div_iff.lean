import Mathlib

#check eq_div_iff
#check div_eq_iff
#check eq_div_iff

example {K : Type} [DivisionRing K] {a b c : K} (hc : c ≠ 0) : a = b / c ↔ a * c = b := by
  simpa [div_eq_mul_inv] using (eq_div_iff hc)

