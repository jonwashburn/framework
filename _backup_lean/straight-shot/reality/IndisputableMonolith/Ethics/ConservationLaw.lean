import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Cost
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Support.GoldenRatio
open IndisputableMonolith

namespace IndisputableMonolith
namespace Ethics
namespace ConservationLaw

open Foundation

-- Use qualified name to avoid ambiguity
local notation "J" => Cost.Jcost

/-! ## Core Theorems on J-Convexity -/

/-- The J-cost functional is zero at unity -/
theorem J_zero_at_one : J 1 = 0 := by
  unfold Cost.Jcost
  simp

/-- The J-cost functional is symmetric: J(x) = J(1/x) -/
theorem J_symmetric (x : ℝ) (hx : 0 < x) : J x = J (1/x) := by
  unfold Cost.Jcost
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h1x : (1 : ℝ) / x ≠ 0 := by positivity
  field_simp [hx0, h1x]
  ring

/-- Auxiliary expression for J showing explicit square scaling. -/
lemma J_sq_div (x : ℝ) (hx : x ≠ 0) :
    J x = (x - 1) ^ 2 / (2 * x) := by
  unfold Cost.Jcost
  field_simp [hx]
  ring

/-- The J-cost functional is nonnegative for positive x -/
theorem J_nonneg (x : ℝ) (hx : 0 < x) : 0 ≤ J x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx_denom : 0 ≤ 2 * x := by
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_nonneg h2 (le_of_lt hx)
  have hx_num : 0 ≤ (x - 1) ^ 2 := by exact sq_nonneg _
  simpa [J_sq_div x hx0] using (div_nonneg hx_num hx_denom)

/-- `J x = 0` iff `x = 1` for positive multipliers. -/
lemma J_eq_zero_iff_one (x : ℝ) (hx : 0 < x) : J x = 0 ↔ x = 1 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h_denom : 0 < 2 * x := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact mul_pos h2 hx
  constructor
  · intro hJ
    have hfrac : (x - 1) ^ 2 / (2 * x) = 0 := by
      simpa [J_sq_div x hx0] using hJ
    have hsq : (x - 1) ^ 2 = 0 := by
      by_contra hneq
      have hpos : 0 < (x - 1) ^ 2 := lt_of_le_of_ne' (sq_nonneg _) hneq
      have : 0 < (x - 1) ^ 2 / (2 * x) := div_pos hpos h_denom
      exact (ne_of_gt this) hfrac
    have hx_sub : x - 1 = 0 := (sq_eq_zero_iff.mp hsq)
    simpa using sub_eq_zero.mp hx_sub
  · intro hx1
    have hx1' : x = 1 := hx1
    simp [hx1', J_sq_div 1 (by norm_num : (1 : ℝ) ≠ 0)]

/-- `J x` is strictly positive away from the minimal point `x = 1`. -/
lemma J_pos_of_ne_one (x : ℝ) (hx : 0 < x) (hne : x ≠ 1) : 0 < J x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [J_sq_div x hx0]
  have h_denom : 0 < 2 * x := by positivity
  have h_num : 0 < (x - 1) ^ 2 := by
    apply sq_pos_of_ne_zero
    intro h
    have : x = 1 := by linarith
    exact hne this
  exact div_pos h_num h_denom

/-- The J-cost functional is strictly convex at x=1. -/
theorem J_strictly_convex_at_one (ε : ℝ) (hε : ε ≠ 0) (h1 : -1 < ε) (h2 : ε < 1) :
  J (1 + ε) + J (1 - ε) > 2 * J 1 := by
  have h1_pos : 0 < 1 + ε := by linarith
  have h2_pos : 0 < 1 - ε := by linarith
  have h1_ne : (1 : ℝ) + ε ≠ 0 := ne_of_gt h1_pos
  have h2_ne : (1 : ℝ) - ε ≠ 0 := ne_of_gt h2_pos
  rw [J_sq_div (1 + ε) h1_ne, J_sq_div (1 - ε) h2_ne, J_zero_at_one]
  simp only [mul_zero]
  have hsum : ((1 + ε) - 1) ^ 2 / (2 * (1 + ε)) + ((1 - ε) - 1) ^ 2 / (2 * (1 - ε)) =
              ε ^ 2 / (2 * (1 + ε)) + ε ^ 2 / (2 * (1 - ε)) := by ring
  rw [hsum]
  have hε2_pos : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
  have h_term1 : 0 < ε ^ 2 / (2 * (1 + ε)) := by positivity
  have h_term2 : 0 < ε ^ 2 / (2 * (1 - ε)) := by positivity
  linarith

/-! ## Pairwise Smoothing Implementation -/

/-- Active bonds directed from agent `i` to agent `j`. -/
noncomputable def bonds_between (s : LedgerState) (i j : AgentId) : Finset BondId :=
  s.active_bonds.filter fun b => s.bond_agents b = some (i, j)

/-- Pairwise skew σᵢⱼ computed as log-flow difference between directions. -/
noncomputable def pairwise_skew (s : LedgerState) (i j : AgentId) : ℝ :=
  (Finset.sum (bonds_between s i j) (fun b => Real.log (s.bond_multipliers b))) -
    (Finset.sum (bonds_between s j i) (fun b => Real.log (s.bond_multipliers b)))

/-- Smooth imbalanced bonds by resetting active multipliers to unity. -/
def smooth_imbalanced_pairs (s : LedgerState) : LedgerState :=
{ s with
  bond_multipliers := fun b => if b ∈ s.active_bonds then 1 else s.bond_multipliers b
  bond_pos := by
    intro b hb
    simp [hb] }

@[simp]
lemma smooth_imbalanced_pairs_active (s : LedgerState) {b : BondId}
    (hb : b ∈ s.active_bonds) :
    (smooth_imbalanced_pairs s).bond_multipliers b = 1 := by
  simp [smooth_imbalanced_pairs, hb]

lemma smooth_imbalanced_pairs_inactive (s : LedgerState) {b : BondId}
    (hb : b ∉ s.active_bonds) :
    (smooth_imbalanced_pairs s).bond_multipliers b = s.bond_multipliers b := by
  simp [smooth_imbalanced_pairs, hb]

/-! ## Recognition Cost and Skew Helpers -/

lemma recognition_cost_nonneg (s : LedgerState) : 0 ≤ RecognitionCost s := by
  unfold RecognitionCost
  apply Finset.sum_nonneg
  intro b hb
  exact J_nonneg (s.bond_multipliers b) (s.bond_pos hb)

lemma recognition_cost_eq_zero_iff (s : LedgerState) :
    RecognitionCost s = 0 ↔ ∀ b ∈ s.active_bonds, s.bond_multipliers b = 1 := by
  unfold RecognitionCost
  constructor
  · intro h b hb
    have hpos := s.bond_pos hb
    have hsum := Finset.sum_eq_zero_iff_of_nonneg (fun b hb => J_nonneg (s.bond_multipliers b) (s.bond_pos hb))
    rw [hsum] at h
    have hJb := h b hb
    exact (J_eq_zero_iff_one (s.bond_multipliers b) hpos).mp hJb
  · intro h
    apply Finset.sum_eq_zero
    intro b hb
    rw [h b hb, J_zero_at_one]

lemma recognition_cost_pos_of_exists {s : LedgerState}
    (h : ∃ b ∈ s.active_bonds, s.bond_multipliers b ≠ 1) :
    0 < RecognitionCost s := by
  obtain ⟨b, hb, hne⟩ := h
  have hpos := s.bond_pos hb
  have hJpos := J_pos_of_ne_one (s.bond_multipliers b) hpos hne
  unfold RecognitionCost
  refine Finset.sum_pos' ?_ ?_
  · intro b' hb'
    exact J_nonneg _ (s.bond_pos hb')
  · exact ⟨b, hb, hJpos⟩

lemma log_eq_zero_iff_eq_one {x : ℝ} (hx : 0 < x) : Real.log x = 0 ↔ x = 1 := by
  constructor
  · intro h
    have := congrArg Real.exp h
    rw [Real.exp_zero, Real.exp_log hx] at this
    exact this
  · intro hx1
    simp [hx1]

lemma reciprocity_skew_abs_nonneg (s : LedgerState) : 0 ≤ Foundation.reciprocity_skew_abs s := by
  classical
  unfold Foundation.reciprocity_skew_abs Foundation.reciprocity_skew
  refine Finset.sum_nonneg ?_
  intro b hb
  exact abs_nonneg _

lemma reciprocity_skew_abs_eq_zero_iff (s : LedgerState) :
    Foundation.reciprocity_skew_abs s = 0 ↔ ∀ b ∈ s.active_bonds, s.bond_multipliers b = 1 := by
  unfold Foundation.reciprocity_skew_abs Foundation.reciprocity_skew signed_log_flow
  constructor
  · intro h b hb
    have hpos := s.bond_pos hb
    have habs_nonneg : ∀ b' ∈ s.active_bonds, 0 ≤ |Real.log (s.bond_multipliers b')| :=
      fun b' _ => abs_nonneg _
    have hsum := Finset.sum_eq_zero_iff_of_nonneg habs_nonneg
    rw [hsum] at h
    have hab := h b hb
    rw [abs_eq_zero] at hab
    exact (log_eq_zero_iff_eq_one hpos).mp hab
  · intro h
    apply Finset.sum_eq_zero
    intro b hb
    rw [h b hb, Real.log_one, abs_zero]

/-! ## Smoothing Helper Lemmas -/

/-- Smoothing achieves σ_abs=0 -/
lemma smooth_achieves_sigma_abs_zero (s : LedgerState) :
  Foundation.reciprocity_skew_abs (smooth_imbalanced_pairs s) = 0 := by
  rw [reciprocity_skew_abs_eq_zero_iff]
  intro b hb
  exact smooth_imbalanced_pairs_active s hb

/-- Smoothing preserves admissibility -/
lemma smooth_preserves_admissible (s : LedgerState) :
  admissible s → admissible (smooth_imbalanced_pairs s) := by
  intro _
  unfold admissible net_skew signed_log_flow
  apply Finset.sum_eq_zero
  intro b hb
  rw [smooth_imbalanced_pairs_active s hb, Real.log_one]

/-- Smoothing lowers cost when σ_abs≠0 -/
lemma smooth_lowers_cost (s : LedgerState)
  (h : Foundation.reciprocity_skew_abs s ≠ 0) :
  RecognitionCost (smooth_imbalanced_pairs s) < RecognitionCost s := by
  have h_exists : ∃ b ∈ s.active_bonds, s.bond_multipliers b ≠ 1 := by
    by_contra h_all
    push_neg at h_all
    have : Foundation.reciprocity_skew_abs s = 0 := (reciprocity_skew_abs_eq_zero_iff s).mpr h_all
    exact h this
  have h_smooth_zero : RecognitionCost (smooth_imbalanced_pairs s) = 0 := by
    rw [recognition_cost_eq_zero_iff]
    intro b hb
    exact smooth_imbalanced_pairs_active s hb
  have h_orig_pos : 0 < RecognitionCost s := recognition_cost_pos_of_exists h_exists
  rw [h_smooth_zero]
  exact h_orig_pos

/-- Alternative formulation: smoothing never increases cost -/
lemma smooth_cost_le (s : LedgerState) :
  RecognitionCost (smooth_imbalanced_pairs s) ≤ RecognitionCost s := by
  by_cases h : Foundation.reciprocity_skew_abs s = 0
  · have h_all : ∀ b ∈ s.active_bonds, s.bond_multipliers b = 1 :=
      (reciprocity_skew_abs_eq_zero_iff s).mp h
    have h_orig_zero : RecognitionCost s = 0 := (recognition_cost_eq_zero_iff s).mpr h_all
    have h_smooth_zero : RecognitionCost (smooth_imbalanced_pairs s) = 0 := by
      rw [recognition_cost_eq_zero_iff]
      intro b hb
      exact smooth_imbalanced_pairs_active s hb
    rw [h_orig_zero, h_smooth_zero]
  · exact le_of_lt (smooth_lowers_cost s h)

/-! ## Pairwise Smoothing -/

theorem pairwise_smoothing_lowers_action (ε : ℝ) (hε : ε ≠ 0) (h1 : -1 < ε) (h2 : ε < 1) :
  J (1 + ε) + J (1 - ε) > J 1 + J 1 := by
  have := J_strictly_convex_at_one ε hε h1 h2
  simpa [two_mul, J_zero_at_one] using this

/-! ## Cycle Minimality -/

theorem cycle_minimal_iff_sigma_abs_zero (s : LedgerState) :
  (∀ s' : LedgerState, admissible s' → RecognitionCost s ≤ RecognitionCost s') ↔
  Foundation.reciprocity_skew_abs s = 0 := by
  classical
  constructor
  · intro h
    by_contra hσ
    have hlt := smooth_lowers_cost s hσ
    have hadd' : admissible (smooth_imbalanced_pairs s) := by
      unfold admissible net_skew signed_log_flow
      apply Finset.sum_eq_zero
      intro b hb
      rw [smooth_imbalanced_pairs_active s hb, Real.log_one]
    have hineq := h (smooth_imbalanced_pairs s) hadd'
    have := lt_of_lt_of_le hlt hineq
    exact lt_irrefl _ this
  · intro hσ s' hs'
    have hall_s : ∀ b ∈ s.active_bonds, s.bond_multipliers b = 1 :=
      (reciprocity_skew_abs_eq_zero_iff s).1 hσ
    have hcost_s : RecognitionCost s = 0 := (recognition_cost_eq_zero_iff s).2 hall_s
    rw [hcost_s]
    exact recognition_cost_nonneg s'

/-! ## Least-Action Dynamics Force σ=0 -/

theorem admissible_forces_net_skew_zero (R : RecognitionOperator) (s : LedgerState) :
  admissible s → net_skew (R.evolve s) = 0 := by
  intro h_adm
  have h_conserved := R.conserves s h_adm
  exact h_conserved

theorem only_net_balanced_admissible (s : LedgerState) :
  admissible s ↔ net_skew s = 0 := by
  rfl

end ConservationLaw
end Ethics
end IndisputableMonolith
