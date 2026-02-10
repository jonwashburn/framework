import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

open Complex
open IndisputableMonolith.LightLanguage.Basis

lemma omega8_pow_re (k : ℕ) : ((omega8 ^ k).re) = Real.cos (k * (Real.pi/4)) := by
  unfold omega8
  rw [← Complex.exp_nat_mul]
  -- after simp, we get cos(↑k * (-pi/4))
  -- rewrite that as cos (-(↑k * (pi/4))) and use cos_neg
  have : (↑k : ℝ) * (-Real.pi / 4) = -((↑k : ℝ) * (Real.pi / 4)) := by ring
  simp [Complex.exp_re, this, Real.cos_neg]

