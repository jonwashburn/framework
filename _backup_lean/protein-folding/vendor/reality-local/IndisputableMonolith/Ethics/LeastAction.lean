import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.ConservationLaw

/-!
# Least-Action Completion (ΠLA)

This module provides a minimal API for least-action completion that projects a
tentative bond assignment back to the σ=0 feasible manifold and (by design)
does not increase recognition cost. For now we provide an identity completion
that satisfies the laws structurally; downstream modules can refine `complete`.
-/

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
theorem leastActionUpdate_eq_base_of_admissible_theorem
    {s : LedgerState} {mods : Finset BondId} {assign : BondId → ℝ}
    (hσ : admissible s) {b : BondId} (hb : b ∈ s.active_bonds) :
    leastActionUpdate s mods assign b = s.bond_multipliers b := by
  unfold leastActionUpdate
  by_cases hmem : b ∈ mods
  · simp only [hmem, dif_pos]
    -- Need to show candidateCost < baseCost is false
    -- admissible s means reciprocity_skew s = 0
    -- This means ∑ |log(bond_multipliers b)| = 0
    -- So |log(bond_multipliers b)| = 0 for each b, meaning bond_multipliers b = 1
    have h_mult_one : s.bond_multipliers b = 1 := by
      unfold admissible reciprocity_skew at hσ
      -- Sum of nonneg reals = 0 means each term = 0
      have h_sum_zero := hσ
      have h_nonneg : ∀ b' ∈ s.active_bonds, 0 ≤ |Real.log (s.bond_multipliers b')| :=
        fun _ _ => abs_nonneg _
      have h_each_zero := Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h_sum_zero b hb
      have h_log_zero : Real.log (s.bond_multipliers b) = 0 := abs_eq_zero.mp h_each_zero
      -- For positive x, log x = 0 iff x = 1 (ruling out x = 0 and x = -1)
      have h_pos := s.bond_pos hb
      rcases Real.log_eq_zero.mp h_log_zero with h0 | h1 | hneg1
      · exact absurd h0 (ne_of_gt h_pos)
      · exact h1
      · exact absurd hneg1 (ne_of_gt (neg_one_lt_zero.trans h_pos))
    -- With bond_multipliers b = 1, baseCost = Jcost(1) = 0
    have h_base_zero : Cost.Jcost (s.bond_multipliers b) = 0 := by
      rw [h_mult_one]
      exact Jcost_unit0
    -- Jcost ≥ 0 for positive inputs, and candidate is positive
    have h_cand_pos : 0 < s.bond_multipliers b * Real.exp (assign b) :=
      mul_pos (s.bond_pos hb) (Real.exp_pos _)
    have h_cand_nonneg : 0 ≤ Cost.Jcost (s.bond_multipliers b * Real.exp (assign b)) :=
      Jcost_nonneg h_cand_pos
    -- candidateCost < baseCost = 0 would require candidateCost < 0, contradiction
    have h_not_lt : ¬(Cost.Jcost (s.bond_multipliers b * Real.exp (assign b)) < Cost.Jcost (s.bond_multipliers b)) := by
      rw [h_base_zero]
      exact not_lt.mpr h_cand_nonneg
    simp only [h_not_lt, if_false]
  · simp only [hmem, dif_neg, not_false_eq_true]

/-- Backward compatibility alias -/
theorem leastActionUpdate_eq_base_of_admissible
    {s : LedgerState} {mods : Finset BondId} {assign : BondId → ℝ}
    (hσ : admissible s) {b : BondId} (hb : b ∈ s.active_bonds) :
    leastActionUpdate s mods assign b = s.bond_multipliers b :=
  leastActionUpdate_eq_base_of_admissible_theorem hσ hb

lemma leastActionUpdate_cost_le
    (s : LedgerState) (mods : Finset BondId) (assign : BondId → ℝ)
    (b : BondId) :
    Cost.Jcost (leastActionUpdate s mods assign b) ≤ Cost.Jcost (s.bond_multipliers b) := by
  unfold leastActionUpdate
  simp only
  split_ifs with hmem hcost
  · exact le_of_lt hcost
  · exact le_refl _
  · exact le_refl _

noncomputable def leastActionComplete
    (s : LedgerState) (mods : Finset BondId) (assign : BondId → ℝ) : LedgerState :=
{ s with
  bond_multipliers := leastActionUpdate s mods assign
  bond_pos := fun hb => leastActionUpdate_pos s mods assign hb }

/-- Least-action completion interface. -/
structure LACompletion where
  /-- Complete tentative assignments on a finite set of bonds, returning a new state. -/
  complete : LedgerState → Finset BondId → (BondId → ℝ) → LedgerState

  /-- Feasibility: admissible states remain admissible after completion. -/
  preserves_sigma_zero : ∀ s mods assign, admissible s → admissible (complete s mods assign)

  /-- Minimality: completion does not increase recognition cost. -/
  minimizes_J : ∀ s mods assign, RecognitionCost (complete s mods assign) ≤ RecognitionCost s

  /-- Locality: bonds outside `mods` are not changed by completion. -/
  locality : ∀ s mods assign b, b ∉ mods →
    (complete s mods assign).bond_multipliers b = s.bond_multipliers b

/-- Identity least-action completion (placeholder consistent with the laws). -/
def identityLACompletion : LACompletion where
  complete := fun s _ _ => s
  preserves_sigma_zero := by
    intro s mods assign h; simpa using h
  minimizes_J := by
    intro s mods assign; exact le_rfl
  locality := by
    intro s mods assign b hb; rfl

/-- Least-action completion that exponentially applies assignments and accepts
updates only when they strictly reduce the local J-cost. -/
noncomputable def leastActionCompletion : LACompletion where
  complete := leastActionComplete
  preserves_sigma_zero := by
    intro s mods assign hσ
    unfold admissible leastActionComplete reciprocity_skew at *
    simp only
    have heq : ∀ b ∈ s.active_bonds,
        |Real.log (leastActionUpdate s mods assign b)| = |Real.log (s.bond_multipliers b)| := by
      intro b hb
      rw [leastActionUpdate_eq_base_of_admissible hσ hb]
    rw [Finset.sum_congr rfl heq]
    exact hσ
  minimizes_J := by
    intro s mods assign
    unfold RecognitionCost leastActionComplete
    simp only
    apply Finset.sum_le_sum
    intro b _
    exact leastActionUpdate_cost_le s mods assign b
  locality := by
    intro s mods assign b hb
    unfold leastActionComplete leastActionUpdate
    simp only [hb, dif_neg, not_false_eq_true]

end Ethics
end IndisputableMonolith
