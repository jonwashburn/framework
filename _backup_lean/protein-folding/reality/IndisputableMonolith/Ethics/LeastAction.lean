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
def leastActionUpdate
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
  classical
  unfold leastActionUpdate
  split_ifs with hmem hcmp
  ·
    have hbase : 0 < s.bond_multipliers b := s.bond_pos hb
    have : 0 < s.bond_multipliers b * Real.exp (assign b) :=
      mul_pos hbase (Real.exp_pos _)
    exact this
  · exact s.bond_pos hb
  · exact s.bond_pos hb

lemma leastActionUpdate_eq_base_of_admissible
    {s : LedgerState} {mods : Finset BondId} {assign : BondId → ℝ}
    (hσ : admissible s) {b : BondId} (hb : b ∈ s.active_bonds) :
    leastActionUpdate s mods assign b = s.bond_multipliers b := by
  classical
  unfold leastActionUpdate
  split_ifs with hmem hcmp
  ·
    -- Under admissibility, all active bond multipliers equal 1.
    have hmul : s.bond_multipliers b = 1 :=
      (reciprocity_skew_eq_zero_iff s |>.1)
        (by simpa [Foundation.admissible] using hσ) b hb
    have hcandidate_nonneg : 0 ≤ Cost.Jcost (s.bond_multipliers b * Real.exp (assign b)) := by
      have hpos : 0 < s.bond_multipliers b * Real.exp (assign b) :=
        by
          have base_pos : 0 < s.bond_multipliers b := by simpa [hmul] using s.bond_pos hb
          exact mul_pos base_pos (Real.exp_pos _)
      exact Cost.Jcost_nonneg hpos
    have : ¬ Cost.Jcost (s.bond_multipliers b * Real.exp (assign b)) < Cost.Jcost (s.bond_multipliers b) := by
      have hbase0 : Cost.Jcost (s.bond_multipliers b) = 0 := by simpa [hmul, Cost.Jcost_unit0]
      have hnot : ¬ (Cost.Jcost (s.bond_multipliers b * Real.exp (assign b)) < 0) :=
        by exact not_lt_of_ge hcandidate_nonneg
      simpa [hbase0] using hnot
    exact (if_neg this)
  · rfl
  · rfl

lemma leastActionUpdate_cost_le
    (s : LedgerState) (mods : Finset BondId) (assign : BondId → ℝ)
    (b : BondId) :
    Cost.Jcost (leastActionUpdate s mods assign b) ≤ Cost.Jcost (s.bond_multipliers b) := by
  classical
  unfold leastActionUpdate
  split_ifs with hmem hcmp
  ·
    -- Candidate chosen only when it strictly lowers cost.
    have hlt : Cost.Jcost (s.bond_multipliers b * Real.exp (assign b)) < Cost.Jcost (s.bond_multipliers b) := hcmp
    exact (le_of_lt hlt)
  · exact le_of_eq rfl
  · exact le_of_eq rfl

def leastActionComplete
    (s : LedgerState) (mods : Finset BondId) (assign : BondId → ℝ) : LedgerState :=
{ s with
  bond_multipliers := leastActionUpdate s mods assign
, bond_pos := by
    intro b hb
    simpa using leastActionUpdate_pos s mods assign hb }

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
def leastActionCompletion : LACompletion where
  complete := leastActionComplete
  preserves_sigma_zero := by
    intro s mods assign hσ
    unfold leastActionComplete
    -- Show every active bond multiplier is unchanged under admissibility.
    have h_eq :
        ∀ b ∈ s.active_bonds,
          leastActionUpdate s mods assign b = s.bond_multipliers b :=
      by intro b hb; exact leastActionUpdate_eq_base_of_admissible hσ hb
    -- Reciprocity skew is unchanged, hence remains zero.
    unfold Foundation.admissible at hσ ⊢
    unfold Foundation.reciprocity_skew at hσ ⊢
    have hsum :
        ∑ b in s.active_bonds, |Real.log (leastActionUpdate s mods assign b)|
          = ∑ b in s.active_bonds, |Real.log (s.bond_multipliers b)| := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      have := h_eq b hb
      simp [this]
    simpa [hsum] using hσ
  minimizes_J := by
    intro s mods assign
    unfold leastActionComplete
    unfold RecognitionCost
    refine
      Finset.sum_le_sum ?_ -- compare bond-wise contributions
    intro b hb
    simpa using leastActionUpdate_cost_le s mods assign b
  locality := by
    intro s mods assign b hb
    unfold leastActionComplete leastActionUpdate
    simp [hb]

end Ethics
end IndisputableMonolith
