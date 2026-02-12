import Mathlib
import IndisputableMonolith.Consciousness.SubstrateSuitability

/-!
# Timing: Hazard, Expected Waiting Time, and Bounds
-/

namespace IndisputableMonolith.Consciousness

/-- Expected time to reformation under Poisson arrivals with success probability p. -/
noncomputable def expectedTimeRebirth (lambda_match p_match : ℝ) : ℝ :=
  1 / (lambda_match * p_match)

lemma expected_time_positive {lam p : ℝ}
  (h : 0 < lam ∧ 0 < p ∧ p ≤ 1) : expectedTimeRebirth lam p > 0 := by
  have hp : 0 < lam * p := by nlinarith
  have : 0 < 1 / (lam * p) := one_div_pos.mpr hp
  simpa [expectedTimeRebirth] using this

/-- Exact formula under positive hazard: E[T] = 1/(λ p). -/
lemma expected_time_eq {lam p : ℝ}
  (h : 0 < lam ∧ 0 < p ∧ p ≤ 1) : expectedTimeRebirth lam p = 1 / (lam * p) := by
  simp [expectedTimeRebirth]

end IndisputableMonolith.Consciousness
