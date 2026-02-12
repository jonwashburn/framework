import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.LightLanguage.Basis.DFT8

open Complex
open IndisputableMonolith.Constants
open IndisputableMonolith.LightLanguage.Basis

namespace Scratch

lemma normSq_phi_mul_omega (n : ℕ) :
    Complex.normSq (omega8 ^ n * (phi : ℂ) - 1)
      = (phi^2 : ℝ) + 1 - 2 * (phi * (omega8 ^ n).re) := by
  -- use normSq_sub with w=1
  have h := Complex.normSq_sub (omega8 ^ n * (phi : ℂ)) (1 : ℂ)
  -- simplify normSq 1 and starRingEnd 1
  --
  --
  --
  --
  --
  --
  --
  --
  --
  --
  --
  --
  simp [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal, Complex.mul_re] at h
  -- h now should be our goal
  simpa using h

end Scratch
