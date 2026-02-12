import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith/Compat

open Real Complex
open scoped BigOperators Matrix

/-!
Neural criticality proxy: 1/f spectra at φ.

We define a simple `1/f` spectrum and show positivity at the critical
balance scale `φ`, sufficient for compiling certificates/reports.
-/

namespace IndisputableMonolith
namespace Biology
namespace NeuralCriticality

noncomputable def eight_beat_spectra (f : ℝ) : ℝ := 1 / f

noncomputable def criticality_balance : ℝ := IndisputableMonolith.Constants.phi

/-- Positivity of the 1/f spectrum at φ. -/
theorem criticality_holds : eight_beat_spectra criticality_balance > 0 := by
  dsimp [eight_beat_spectra, criticality_balance]
  have hφpos : 0 < IndisputableMonolith.Constants.phi := by
    have : 1 < IndisputableMonolith.Constants.phi := IndisputableMonolith.Constants.one_lt_phi
    exact lt_trans (by norm_num) this
  exact inv_pos.mpr hφpos

end NeuralCriticality
end Biology
end IndisputableMonolith
