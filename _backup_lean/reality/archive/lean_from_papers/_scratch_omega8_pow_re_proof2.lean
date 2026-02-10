import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

open Complex
open IndisputableMonolith.LightLanguage.Basis

namespace Scratch

lemma omega8_pow_re (n : ℕ) : (omega8 ^ n).re = Real.cos (Real.pi * n / 4) := by
  unfold omega8
  simp only [← Complex.exp_nat_mul]
  -- rewrite nat scalar into a real*I form
  have h : (n : ℕ) * (-Complex.I * Real.pi / 4) = ((-(Real.pi * n / 4)) : ℝ) * Complex.I := by
    push_cast
    ring
  rw [h]
  -- now apply exp_ofReal_mul_I_re
  -- exp((-(pi*n/4))*I).re = cos (-(pi*n/4))
  have : (Complex.exp ((-(Real.pi * n / 4)) * Complex.I)).re = Real.cos (-(Real.pi * n / 4)) := by
    simpa using (Complex.exp_ofReal_mul_I_re (-(Real.pi * n / 4)))
  -- finish
  simpa [Real.cos_neg, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using this

end Scratch
