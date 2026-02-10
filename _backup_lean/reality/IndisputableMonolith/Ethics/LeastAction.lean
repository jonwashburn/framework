import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.ConservationLaw

namespace IndisputableMonolith
namespace Ethics

open Foundation
open ConservationLaw
open Cost

open scoped Classical

/-- Internal helper: apply a tentative exponential assignment and accept it only
if it strictly lowers the local J-cost. -/
noncomputable def leastActionUpdate
    (s : LedgerState)
    (mods : Finset BondId)
    (assign : BondId → ℝ)
    (b : BondId) : ℝ :=
  if hmem : b ∈ mods then
    let base := s.bond_multipliers b
    let candidate := base * Real.exp (assign b)
    let candidateCost := Cost.Jcost candidate
    let baseCost := Cost.Jcost base
    if candidateCost < baseCost then candidate else base
  else
    s.bond_multipliers b

lemma leastActionUpdate_pos
    (s : LedgerState) (mods : Finset BondId) (assign : BondId → ℝ)
    {b : BondId} (hb : b ∈ s.active_bonds) :
    0 < leastActionUpdate s mods assign b := by
  unfold leastActionUpdate
  by_cases hmem : b ∈ mods
  · simp only [hmem, dif_pos]
    by_cases hcost : Cost.Jcost (s.bond_multipliers b * Real.exp (assign b)) < Cost.Jcost (s.bond_multipliers b)
    · simp only [hcost, if_true]
      exact mul_pos (s.bond_pos hb) (Real.exp_pos _)
    · simp only [hcost, if_false]
      exact s.bond_pos hb
  · simp only [hmem, dif_neg, not_false_eq_true]
    exact s.bond_pos hb

/-- For admissible states, all bond multipliers are 1, so Jcost(base) = 0.
Since Jcost ≥ 0 everywhere, candidate cost cannot be < base cost. -/
theorem leastActionUpdate_eq_base_of_admissible
    {s : LedgerState} {mods : Finset BondId} {assign : BondId → ℝ}
    (h_bal : reciprocity_skew_abs s = 0) {b : BondId} (hb : b ∈ s.active_bonds) :
    leastActionUpdate s mods assign b = s.bond_multipliers b := by
  unfold leastActionUpdate
  by_cases hmem : b ∈ mods
  · simp only [hmem, dif_pos]
    have h_mult_one : s.bond_multipliers b = 1 := by
      rw [reciprocity_skew_abs_eq_zero_iff] at h_bal
      exact h_bal b hb
    have h_base_zero : Cost.Jcost (s.bond_multipliers b) = 0 := by
      rw [h_mult_one]
      exact J_zero_at_one
    have h_cand_pos : 0 < s.bond_multipliers b * Real.exp (assign b) :=
      mul_pos (s.bond_pos hb) (Real.exp_pos _)
    have h_cand_nonneg : 0 ≤ Cost.Jcost (s.bond_multipliers b * Real.exp (assign b)) :=
      J_nonneg _ h_cand_pos
    have h_not_lt : ¬(Cost.Jcost (s.bond_multipliers b * Real.exp (assign b)) < Cost.Jcost (s.bond_multipliers b)) := by
      rw [h_base_zero]
      exact not_lt.mpr h_cand_nonneg
    simp only [h_not_lt, if_false]
  · simp only [hmem, dif_neg, not_false_eq_true]

lemma leastActionUpdate_cost_le
    (s : LedgerState) (mods : Finset BondId) (assign : BondId → ℝ)
    (b : BondId) :
    Cost.Jcost (leastActionUpdate s mods assign b) ≤ Cost.Jcost (s.bond_multipliers b) := by
  unfold leastActionUpdate
  simp only
  split_ifs with _ hcost
  · exact le_of_lt hcost
  · exact le_refl _
  · exact le_refl _

/-- Least-action completion interface. -/
structure LACompletion where
  complete : LedgerState → Finset BondId → (BondId → ℝ) → LedgerState
  preserves_sigma_zero : ∀ s mods assign, admissible s → admissible (complete s mods assign)
  minimizes_J : ∀ s mods assign, RecognitionCost (complete s mods assign) ≤ RecognitionCost s
  locality : ∀ s mods assign b, b ∉ mods →
    (complete s mods assign).bond_multipliers b = s.bond_multipliers b

/-- Identity least-action completion (placeholder consistent with the laws). -/
def identityLACompletion : LACompletion where
  complete := fun s _ _ => s
  preserves_sigma_zero := by
    intro s mods assign h; exact h
  minimizes_J := by
    intro s mods assign; exact le_rfl
  locality := by
    intro s mods assign b _; rfl

/-- Final Least-Action Completion for the session.
    Uses identity to satisfy strict locality while a projection-based
    local update is developed. -/
def leastActionCompletion : LACompletion := identityLACompletion

end Ethics
end IndisputableMonolith
