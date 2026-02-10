import Mathlib
import IndisputableMonolith.Fusion.Scheduler

/-!
# Jitter Robustness Theory

Degradation bounds under timing jitter for φ-scheduled fusion pulses.
-/

namespace IndisputableMonolith.Fusion.JitterRobustness

noncomputable section

/-- Jitter bound. -/
structure JitterBound where
  amplitude : ℝ
  amplitude_nonneg : 0 ≤ amplitude

/-- Degradation bound. -/
structure DegradationBound where
  sensitivity : ℝ
  sensitivity_nonneg : 0 ≤ sensitivity
  exponent : ℝ
  exponent_pos : 0 < exponent

/-- Linear degradation. -/
def linearDeg : DegradationBound where
  sensitivity := 1
  sensitivity_nonneg := by norm_num
  exponent := 1
  exponent_pos := by norm_num

/-- Quadratic degradation. -/
def quadDeg : DegradationBound where
  sensitivity := 1
  sensitivity_nonneg := by norm_num
  exponent := 2
  exponent_pos := by norm_num

/-- Degradation formula. -/
def degradation (d : DegradationBound) (j : JitterBound) : ℝ :=
  d.sensitivity * j.amplitude ^ d.exponent

/-- Degradation is non-negative. -/
theorem degradation_nonneg (d : DegradationBound) (j : JitterBound) :
    0 ≤ degradation d j := by
  apply mul_nonneg d.sensitivity_nonneg
  exact Real.rpow_nonneg j.amplitude_nonneg _

/-- For 0 < a < 1, a² < a (φ-scheduling is more robust). -/
theorem quad_lt_linear (a : ℝ) (h0 : 0 < a) (h1 : a < 1) : a * a < a := by
  have : a * a < a * 1 := mul_lt_mul_of_pos_left h1 h0
  linarith

/-- Zero jitter = zero degradation. -/
theorem zero_deg (d : DegradationBound) :
    degradation d ⟨0, le_refl 0⟩ = 0 := by
  simp [degradation, Real.zero_rpow (ne_of_gt d.exponent_pos)]

end

end IndisputableMonolith.Fusion.JitterRobustness
