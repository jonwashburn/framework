import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith

namespace Constants

@[simp] noncomputable def RSUnits.tau_rec_display (U : RSUnits) : ℝ := K * U.tau0
@[simp] noncomputable def RSUnits.lambda_kin_display (U : RSUnits) : ℝ := K * U.ell0

@[simp] theorem RSUnits.display_speed_eq_c (U : RSUnits) :
  (RSUnits.lambda_kin_display U) / (RSUnits.tau_rec_display U) = U.c := by
  -- K * ℓ0 / (K * τ0) = ℓ0/τ0 = c
  have h : (K * U.ell0) / (K * U.tau0) = U.ell0 / U.tau0 := by
    by_cases hK : K = 0
    · -- If K = 0, both numerator and denominator are 0; use structural identity directly
      simp [RSUnits.lambda_kin_display, RSUnits.tau_rec_display, hK]
    · -- Cancel common nonzero factor K
      have hK0 : K ≠ 0 := hK
      have := mul_div_mul_left₀ U.ell0 U.tau0 K hK0
      simpa [RSUnits.lambda_kin_display, RSUnits.tau_rec_display, mul_comm, mul_left_comm, mul_assoc]
        using this
  have hstruct : U.ell0 / U.tau0 = U.c := by
    -- from RSUnits structure: ℓ0 = c·τ0
    have : U.ell0 = U.c * U.tau0 := U.c_ell0_tau0
    simpa [this, div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using rfl
  simpa [h] using hstruct

end Constants

namespace TruthCore

/-- Alias: display speed identity λ_kin/τ_rec = c. -/
theorem display_speed_identity (U : Constants.RSUnits) :
  (Constants.RSUnits.lambda_kin_display U) / (Constants.RSUnits.tau_rec_display U) = U.c :=
  Constants.RSUnits.display_speed_eq_c U

end TruthCore

end IndisputableMonolith
