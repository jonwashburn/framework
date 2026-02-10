import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

open Complex
open IndisputableMonolith.LightLanguage.Basis

namespace Scratch

lemma omega8_pow_re (n : ℕ) : (omega8 ^ n).re = Real.cos (Real.pi * n / 4) := by
  unfold omega8
  -- omega8^n = exp (n * (-I*pi/4))
  simp only [← Complex.exp_nat_mul]
  -- rewrite exponent into a real*I form
  have h : (n : ℕ) * (-Complex.I * Real.pi / 4) = ((-(Real.pi * n / 4)) : ℝ) * Complex.I := by
    push_cast
    ring
  -- apply the real-part lemma for exp(x*I)
  -- exp (-(pi*n/4) * I).re = cos (-(pi*n/4)) = cos(pi*n/4)
  --
  rw [h]
  simp [Complex.exp_ofReal_mul_I_re, Real.cos_neg, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]

end Scratch
