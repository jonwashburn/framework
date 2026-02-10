import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Derivation
import IndisputableMonolith.Foundation.RecognitionOperator

/-!
# Constants Consistency Theorems

This module provides consistency checks between different constant definitions
in the codebase and defines SI-calibrated values for external use.

## Unit Convention Note

**RS-native units** (in Foundation): τ₀ = 1 tick, ℓ₀ = 1 voxel, c = 1 voxel/tick.
**SI-calibrated units** (in this module): τ₀ in seconds, for matching to experiments.

## Main Definitions

* `tau0_SI`: The SI-calibrated fundamental tick duration (in seconds)

-/

namespace IndisputableMonolith
namespace Constants
namespace Consistency

noncomputable section

open Real

/-! ## SI-Calibrated τ₀

The SI-based τ₀ value for external calibration checks.
This is √(ℏG/(πc³))/c with CODATA values.

NOTE: This is the SI value in seconds. In RS-native units (Foundation),
τ₀ = 1 tick by definition. Use `RSNativeUnits.ExternalCalibration`
to convert between them. -/
noncomputable def tau0_SI : ℝ :=
  sqrt ((Derivation.hbar_codata) * (Derivation.G_codata) /
        (Real.pi * (Derivation.c_codata) ^ 3)) / Derivation.c_codata

/-- The τ₀_SI matches Derivation.tau0. -/
theorem tau0_SI_eq_derivation : tau0_SI = Derivation.tau0 := by
  unfold tau0_SI Derivation.tau0
  rfl

/-- τ₀_SI is positive. -/
lemma tau0_SI_pos : 0 < tau0_SI := by
  rw [tau0_SI_eq_derivation]
  exact Derivation.tau0_pos

/-- Octave duration in SI units (8 × τ₀_SI). -/
noncomputable def octave_SI : ℝ := 8 * tau0_SI

/-- Octave duration is positive. -/
lemma octave_SI_pos : 0 < octave_SI := by
  unfold octave_SI
  exact mul_pos (by norm_num : (0 : ℝ) < 8) tau0_SI_pos

/-! ## φ-Scaling Verification -/

/-- The golden ratio φ is defined consistently across modules. -/
theorem phi_consistency :
    Constants.phi = Foundation.φ := rfl

/-! ## Summary -/

def consistency_status : String :=
  "✓ tau0_SI defined as SI-calibrated tick duration\n" ++
  "✓ tau0_SI_eq_derivation: matches Derivation.tau0\n" ++
  "✓ tau0_SI_pos: is positive\n" ++
  "✓ phi_consistency: φ matches across modules\n" ++
  "\n" ++
  "NOTE: RS-native units (Foundation.tick = 1) are dimensionless.\n" ++
  "SI values (tau0_SI) are for external calibration only."

#eval consistency_status

end
end Consistency
end Constants
end IndisputableMonolith
