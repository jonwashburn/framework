import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.Constants

open IndisputableMonolith
open IndisputableMonolith.Constants
open IndisputableMonolith.LightLanguage.Basis

example : ‖(omega8 ^ 7 * (phi : ℂ))‖ = phi := by
  have hω : ‖omega8 ^ 7‖ = (1 : ℝ) := by
    have : ‖omega8 ^ 7‖ = ‖omega8‖ ^ 7 := by
      simpa using (Complex.norm_pow omega8 7)
    simpa [this, omega8_abs]
  have hφ : ‖(phi : ℂ)‖ = phi := by
    have : ‖(phi : ℂ)‖ = |phi| := by
      simpa using (RCLike.norm_ofReal (K := ℂ) phi)
    simpa [abs_of_pos phi_pos] using this
  calc
    ‖omega8 ^ 7 * (phi : ℂ)‖ = ‖omega8 ^ 7‖ * ‖(phi : ℂ)‖ := by
      simpa using (norm_mul (omega8 ^ 7) (phi : ℂ))
    _ = 1 * phi := by simp [hω, hφ]
    _ = phi := by ring
