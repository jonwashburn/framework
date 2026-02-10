import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

open Complex
open IndisputableMonolith.LightLanguage.Basis

lemma omega8_pow_re (k : ℕ) : ((omega8 ^ k).re) = Real.cos (k * (Real.pi/4)) := by
  -- omega8 = exp(-I*pi/4)
  unfold omega8
  -- omega8^k = exp(k * (-I*pi/4))
  rw [← Complex.exp_nat_mul]
  -- Real part of exp
  -- exp_re: (cexp z).re = exp z.re * cos z.im
  -- Here z = k * (-I*pi/4) has re=0 and im = -(k*pi/4)
  simp [Complex.exp_re, Real.cos_neg, mul_assoc, mul_left_comm, mul_comm]

