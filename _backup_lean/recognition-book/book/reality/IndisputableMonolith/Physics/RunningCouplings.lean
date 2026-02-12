import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RSBridge.Anchor

/-!
Running-coupling crossover scaffolding: thresholds at φ^r rungs and
an eight-beat plateau scale. Provides positive witnesses used by
certificates and reports.
-/

namespace IndisputableMonolith
namespace Physics

/-- Threshold energy scale at a fermion rung. -/
noncomputable def rung_threshold (f : RSBridge.Fermion) : ℝ :=
  IndisputableMonolith.Constants.E_coh * (IndisputableMonolith.Constants.phi ^ (f.rung : ℝ))

/-- Plateau scale from eight-beat locking (dimensionless). -/
noncomputable def eight_beat_plateau : ℝ :=
  IndisputableMonolith.Constants.phi ^ ((-5 : Int) : ℝ)

/-- Positivity of `rung_threshold`. -/
theorem rung_threshold_pos (f : RSBridge.Fermion) : rung_threshold f > 0 := by
  have hφpos : 0 < IndisputableMonolith.Constants.phi := by
    have : 1 < IndisputableMonolith.Constants.phi := IndisputableMonolith.Constants.one_lt_phi
    exact lt_trans (by norm_num) this
  have hpow : 0 < IndisputableMonolith.Constants.phi ^ (f.rung : ℝ) :=
    Real.rpow_pos_of_pos hφpos _
  have hE : 0 < IndisputableMonolith.Constants.E_coh :=
    IndisputableMonolith.Constants.E_coh_pos
  exact mul_pos hE hpow

/-- Positivity of the eight-beat plateau scale. -/
theorem plateau_pos : eight_beat_plateau > 0 := by
  have hφpos : 0 < IndisputableMonolith.Constants.phi := by
    have : 1 < IndisputableMonolith.Constants.phi := IndisputableMonolith.Constants.one_lt_phi
    exact lt_trans (by norm_num) this
  simpa [eight_beat_plateau] using
    (Real.rpow_pos_of_pos hφpos ((-5 : Int) : ℝ))

/-- Crossover witness: any lighter-rung threshold and the plateau are positive. -/
theorem crossover_holds (heavy light : RSBridge.Fermion)
  (hle : light.rung ≤ heavy.rung) :
  rung_threshold light > 0 ∧ eight_beat_plateau > 0 := by
  exact And.intro (rung_threshold_pos light) plateau_pos

end Physics
end IndisputableMonolith
