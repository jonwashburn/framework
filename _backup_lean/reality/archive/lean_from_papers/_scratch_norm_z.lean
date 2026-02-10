import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.Constants

open IndisputableMonolith
open IndisputableMonolith.Constants
open IndisputableMonolith.LightLanguage.Basis

example : ‖(omega8 ^ 7 * (phi : ℂ))‖ = phi := by
  -- norm of ω is 1
  have hω : ‖omega8 ^ 7‖ = (1 : ℝ) := by
    -- `‖omega8‖ = 1` and `‖z^n‖ = ‖z‖^n`
    have : ‖omega8 ^ 7‖ = ‖omega8‖ ^ 7 := by simpa using (Complex.norm_pow omega8 7)
    -- rewrite `‖omega8‖` using `omega8_abs`
    simpa [this, omega8_abs]
  -- norm of (phi : ℂ) is |phi| = phi since phi > 0
  have hφ : ‖(phi : ℂ)‖ = phi := by
    have : ‖(phi : ℂ)‖ = |phi| := by
      simpa using (RCLike.norm_ofReal (K := ℂ) phi)
    simpa [abs_of_pos phi_pos] using this
  -- combine
  simpa [norm_mul, hω, hφ]
