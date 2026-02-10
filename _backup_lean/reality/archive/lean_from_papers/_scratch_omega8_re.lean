import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8

open Complex
open IndisputableMonolith.LightLanguage.Basis

namespace Scratch

lemma omega8_pow_re (n : ℕ) : (omega8 ^ n).re = Real.cos (Real.pi * n / 4) := by
  -- omega8 = exp (-I*pi/4) = exp ((-(pi/4)) * I)
  unfold omega8
  -- push pow inside exp
  simp only [← Complex.exp_nat_mul]
  -- rewrite the exponent to real*I
  -- n * (-I*pi/4) = (-(pi*n/4)) * I
  have h : (n : ℂ) * (-Complex.I * Real.pi / 4) = ((-(Real.pi * n / 4) : ℝ) : ℂ) * Complex.I := by
    -- treat casts carefully
    push_cast
    ring
  -- use h
  --
  -- now take real part
  --
  -- exp (x*I).re = cos x
  --
  --
  --
  --
  --
  --
  sorry

end Scratch
