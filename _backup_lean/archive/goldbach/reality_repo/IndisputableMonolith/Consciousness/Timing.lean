import Mathlib
import IndisputableMonolith.Consciousness.SubstrateSuitability

/-!
# Timing: Hazard, Expected Waiting Time, and Bounds
-/

namespace IndisputableMonolith.Consciousness

/-- Expected time to reformation under Poisson arrivals with success probability p. -/
def expectedTimeRebirth (lambda_match p_match : ℝ) : ℝ :=
  if 0 < lambda_match ∧ 0 < p_match ∧ p_match ≤ 1 then
    1 / (lambda_match * p_match)
  else
    Real.infinity

lemma expected_time_positive {λ p : ℝ}
  (h : 0 < λ ∧ 0 < p ∧ p ≤ 1) : expectedTimeRebirth λ p > 0 := by
  simp [expectedTimeRebirth, h, inv_pos.mpr]
  have : 0 < λ * p := by nlinarith
  exact this

/-- Exact formula under positive hazard: E[T] = 1/(λ p). -/
lemma expected_time_eq {λ p : ℝ}
  (h : 0 < λ ∧ 0 < p ∧ p ≤ 1) : expectedTimeRebirth λ p = 1 / (λ * p) := by
  simp [expectedTimeRebirth, h]

end IndisputableMonolith.Consciousness
