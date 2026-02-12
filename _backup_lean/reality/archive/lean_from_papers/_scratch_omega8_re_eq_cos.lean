import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

open Complex
open IndisputableMonolith.LightLanguage.Basis

-- Quick check: compute Re(omega8^k) in terms of cos.

lemma omega8_pow_re (k : ℕ) : ((omega8 ^ k).re) = Real.cos (k * (Real.pi/4)) := by
  -- omega8 = exp(-I*pi/4)
  unfold omega8
  -- omega8^k = exp(k * (-I*pi/4))
  rw [← Complex.exp_nat_mul]
  -- Now apply exp_re: Re(exp z) = exp(Re z) * cos(Im z)
  -- Here z = k * (-I*pi/4) has Re=0 and Im = -(k*pi/4).
  simp [Complex.exp_re, mul_assoc, mul_left_comm, mul_comm, mul_add, add_mul]

