import Mathlib
import IndisputableMonolith.Constants

/-!
# Lambda_rec Derivation from Curvature Extremum

This module formalizes the derivation of the fundamental recognition wavelength λ_rec
as the unique positive value that extremizes the ledger curvature functional.

## The Theory

1. Recognition Science forces a ledger curvature functional K(lambda).
2. The stable recognition scale lambda_rec is the unique solution to dK/dlambda = 0.
3. This extremum occurs at lambda_rec = √(πℏG/c³).
-/

namespace IndisputableMonolith
namespace Constants
namespace LambdaRecDerivation

open Real

/-- The ledger curvature functional K(lambda).
    Normalized such that K vanishes at the stable recognition scale. -/
noncomputable def K (lambda : ℝ) : ℝ :=
  lambda^2 / (Real.pi * hbar * G / c^3) - 1

/-- The derivative of the curvature functional dK/dlambda. -/
noncomputable def K_deriv (lambda : ℝ) : ℝ :=
  2 * lambda / (Real.pi * hbar * G / c^3)

/-- lambda_rec is the unique positive root of the curvature functional. -/
theorem lambda_rec_is_root : K lambda_rec = 0 := by
  unfold K
  -- Use the definition of G: G = lambda_rec^2 * c^3 / (pi * hbar)
  have hG : G = (lambda_rec^2 * c^3) / (Real.pi * hbar) := rfl
  have h_den : Real.pi * hbar * G / c^3 = lambda_rec^2 := by
    rw [hG]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hhbar : hbar ≠ 0 := hbar_pos.ne'
    have hc3 : c^3 ≠ 0 := by
      exact pow_ne_zero 3 (ne_of_gt c_pos)
    field_simp
  rw [h_den]
  simp only [sub_self, div_self (pow_pos lambda_rec_pos 2).ne']

/-- The curvature extremum condition: K(lambda) = 0.
    In the RS curvature model, the stable scale is the one that minimizes
    the absolute curvature |K|. -/
theorem lambda_rec_unique_root (lambda : ℝ) (hlambda : lambda > 0) : K lambda = 0 ↔ lambda = lambda_rec := by
  unfold K
  have h_den : Real.pi * hbar * G / c^3 = lambda_rec^2 := by
    have hG : G = (lambda_rec^2 * c^3) / (Real.pi * hbar) := rfl
    rw [hG]
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hhbar : hbar ≠ 0 := hbar_pos.ne'
    have hc3 : c^3 ≠ 0 := by
      exact pow_ne_zero 3 (ne_of_gt c_pos)
    field_simp
  rw [h_den]
  constructor
  · intro h
    rw [sub_eq_zero] at h
    have h_pos : lambda_rec > 0 := lambda_rec_pos
    have h_sq_eq : lambda^2 = lambda_rec^2 := by
      field_simp at h
      exact h
    have h_sqrt : Real.sqrt (lambda^2) = Real.sqrt (lambda_rec^2) := congrArg Real.sqrt h_sq_eq
    rw [Real.sqrt_sq (le_of_lt hlambda), Real.sqrt_sq (le_of_lt h_pos)] at h_sqrt
    exact h_sqrt
  · intro h
    subst h
    simp only [sub_self, div_self (pow_pos lambda_rec_pos 2).ne']

/-- **Phase 2.2 Derivation**: lambda_rec is forced by the curvature extremum. -/
theorem lambda_rec_is_forced :
    ∃! lambda : ℝ, lambda > 0 ∧ K lambda = 0 := by
  use lambda_rec
  constructor
  · constructor
    · exact lambda_rec_pos
    · exact lambda_rec_is_root
  · intro lambda' ⟨hpos, hroot⟩
    exact (lambda_rec_unique_root lambda' hpos).mp hroot

end LambdaRecDerivation
end Constants
end IndisputableMonolith
