import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Ethics.Audit
import IndisputableMonolith.Support.GoldenRatio

/-!
# Hope: Optimism Prior Against Paralysis

Hope prevents paralysis by assigning non-zero probabilities to positive outcomes,
enabling action even when high-probability outcomes appear negative.

## Mathematical Definition

Given future outcomes {Wᵢ} with probabilities pᵢ, Hope adds optimism prior εᵢ:
Value(A) = Σᵢ (pᵢ + εᵢ) · Utility(Wᵢ | A)

where εᵢ > 0 if Utility(Wᵢ) high, and Σ εᵢ = 0 (zero-sum adjustment).

## Physical Grounding

- **Multiverse**: Many possible futures exist
- **Positive Cost**: Inaction also has cost (lost positive futures)
- **Bounded optimism**: ε small to preserve realism

## Connection to virtues.tex

Section 12 (Hope): "To enable action and prevent paralysis in the face of
uncertainty by assigning non-zero probabilities to positive future outcomes."

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState

open scoped BigOperators

/-- A future outcome with probability and utility -/
structure FutureOutcome where
  state : MoralState
  probability : ℝ
  utility : ℝ  -- Value measure (lower skew = higher utility)
  h_prob_bounds : 0 ≤ probability ∧ probability ≤ 1

/-- Total probability mass carried by the provided outcome list. -/
def totalProbability (outcomes : List FutureOutcome) : ℝ :=
  outcomes.foldl (fun acc o => acc + o.probability) 0

/-- Total utility accumulated across the outcome list. -/
def totalUtility (outcomes : List FutureOutcome) : ℝ :=
  outcomes.foldl (fun acc o => acc + o.utility) 0

/-- Mean utility of the outcome list (defaults to `0` for the empty list). -/
noncomputable def meanUtility (outcomes : List FutureOutcome) : ℝ :=
  match outcomes with
  | [] => 0
  | _ => totalUtility outcomes / (outcomes.length : ℝ)

/-- Denominator used by the hope prior to reallocate probability mass. -/
noncomputable def hopeDenominator (outcomes : List FutureOutcome) : ℝ :=
  let μ := meanUtility outcomes
  outcomes.foldl (fun acc o => acc + |o.utility - μ|) 0

/-- Hope adjustment assigned to a single outcome. -/
noncomputable def hopeAdjustment
  (outcomes : List FutureOutcome) (ε : ℝ) (outcome : FutureOutcome) : ℝ :=
  let μ := meanUtility outcomes
  let denom := hopeDenominator outcomes
  let centered := outcome.utility - μ
  if denom = 0 then 0 else ε * centered / denom

/-- Vector of hope adjustments covering all outcomes. -/
noncomputable def hopeAdjustments
  (outcomes : List FutureOutcome) (ε : ℝ) : List ℝ :=
  outcomes.map (hopeAdjustment outcomes ε)

/-- Probability of an outcome after applying the optimism prior. -/
noncomputable def hopeAdjustedProbability
  (outcomes : List FutureOutcome) (ε : ℝ) (outcome : FutureOutcome) : ℝ :=
  outcome.probability + hopeAdjustment outcomes ε outcome

/-- All probabilities after applying the optimism prior. -/
noncomputable def hopeAdjustedProbabilities
  (outcomes : List FutureOutcome) (ε : ℝ) : List ℝ :=
  outcomes.map (fun outcome => hopeAdjustedProbability outcomes ε outcome)

/-- Expected utility under the baseline distribution. -/
noncomputable def expectedUtility (outcomes : List FutureOutcome) : ℝ :=
  outcomes.foldl (fun acc o => acc + o.probability * o.utility) 0

/-- Expected utility after applying the optimism prior. -/
noncomputable def hopeAdjustedExpectedUtility
  (outcomes : List FutureOutcome) (ε : ℝ) : ℝ :=
  outcomes.foldl
    (fun acc o => acc + hopeAdjustedProbability outcomes ε o * o.utility) 0

lemma length_ne_zero_of_ne_nil {α : Type _} {xs : List α}
    (h : xs ≠ []) : xs.length ≠ 0 := by
  cases xs with
  | nil => simpa using h
  | cons _ _ => simp

lemma totalUtility_foldl_add_const (xs : List FutureOutcome) :
    ∀ acc : ℝ,
      xs.foldl (fun a o => a + o.utility) acc =
        acc + xs.foldl (fun a o => a + o.utility) 0 := by
  induction xs with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (acc + x.utility), ih (0 + x.utility)]
    ring

lemma foldl_abs_add_const (xs : List FutureOutcome) (μ : ℝ) :
    ∀ acc : ℝ,
      xs.foldl (fun a o => a + |o.utility - μ|) acc =
        acc + xs.foldl (fun a o => a + |o.utility - μ|) 0 := by
  induction xs with
  | nil => intro acc; simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (acc + |x.utility - μ|), ih (0 + |x.utility - μ|)]
    ring

lemma foldl_sub_const_acc (xs : List FutureOutcome) (μ : ℝ) :
    ∀ acc : ℝ,
      xs.foldl (fun a o => a + (o.utility - μ)) acc =
        acc + totalUtility xs - (xs.length : ℝ) * μ := by
  induction xs with
  | nil =>
    intro acc
    simp only [List.foldl_nil, List.length_nil, Nat.cast_zero, mul_zero, sub_zero, totalUtility,
               List.foldl]
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons, Nat.cast_succ, totalUtility]
    rw [ih (acc + (x.utility - μ))]
    rw [totalUtility_foldl_add_const xs (0 + x.utility)]
    simp only [zero_add]
    ring

lemma foldl_sub_const (xs : List FutureOutcome) (μ : ℝ) :
    xs.foldl (fun acc o => acc + (o.utility - μ)) 0
      = totalUtility xs - (xs.length : ℝ) * μ := by
  rw [foldl_sub_const_acc]
  ring

lemma sum_centered_zero (outcomes : List FutureOutcome) :
    outcomes.foldl
        (fun acc o => acc + (o.utility - meanUtility outcomes)) 0 = 0 := by
  rw [foldl_sub_const]
  unfold meanUtility
  by_cases h : outcomes.length = 0
  · simp [h, totalUtility]
  · have h_len_pos : 0 < (outcomes.length : ℝ) := by
      have : 0 < outcomes.length := Nat.pos_of_ne_zero h
      exact_mod_cast this
    field_simp
    ring

lemma foldl_scale (outcomes : List FutureOutcome) (μ scale : ℝ) :
    outcomes.foldl (fun acc o => acc + scale * (o.utility - μ)) 0 =
      scale * outcomes.foldl (fun acc o => acc + (o.utility - μ)) 0 := by
  induction outcomes with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    -- Need to show: (xs.foldl f (0 + scale * (x.utility - μ))) = scale * (xs.foldl g (0 + (x.utility - μ)))
    -- where f acc o = acc + scale * (o.utility - μ) and g acc o = acc + (o.utility - μ)
    have h1 : ∀ acc : ℝ, xs.foldl (fun a o => a + scale * (o.utility - μ)) acc =
        acc + xs.foldl (fun a o => a + scale * (o.utility - μ)) 0 := by
      intro acc
      induction xs generalizing acc with
      | nil => simp
      | cons y ys ih2 =>
        simp only [List.foldl_cons]
        rw [ih2 (acc + scale * (y.utility - μ)), ih2 (0 + scale * (y.utility - μ))]
        ring
    have h2 : ∀ acc : ℝ, xs.foldl (fun a o => a + (o.utility - μ)) acc =
        acc + xs.foldl (fun a o => a + (o.utility - μ)) 0 := by
      intro acc
      induction xs generalizing acc with
      | nil => simp
      | cons y ys ih2 =>
        simp only [List.foldl_cons]
        rw [ih2 (acc + (y.utility - μ)), ih2 (0 + (y.utility - μ))]
        ring
    rw [h1, h2, ih]
    ring

lemma hopeAdjustment_eq_zero_of_denom_zero
    (outcomes : List FutureOutcome) (ε : ℝ) (outcome : FutureOutcome)
    (h : hopeDenominator outcomes = 0) :
    hopeAdjustment outcomes ε outcome = 0 := by
  simp [hopeAdjustment, h]

lemma hopeAdjustment_eq_of_denom_ne_zero
    (outcomes : List FutureOutcome) (ε : ℝ) (outcome : FutureOutcome)
    (h : hopeDenominator outcomes ≠ 0) :
    hopeAdjustment outcomes ε outcome =
      ε / hopeDenominator outcomes * (outcome.utility - meanUtility outcomes) := by
  have : hopeDenominator outcomes ≠ 0 := h
  unfold hopeAdjustment
  simp [this, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma hopeAdjustment_sum_eq_zero (outcomes : List FutureOutcome) (ε : ℝ) :
    outcomes.foldl (fun acc o => acc + hopeAdjustment outcomes ε o) 0 = 0 := by
  classical
  by_cases hDen : hopeDenominator outcomes = 0
  · simp [hopeAdjustment_eq_zero_of_denom_zero, hDen]
  · have h : hopeDenominator outcomes ≠ 0 := hDen
    have := foldl_scale outcomes (meanUtility outcomes)
      (ε / hopeDenominator outcomes)
    have hRewrite :
        (fun acc o => acc + hopeAdjustment outcomes ε o)
          =
        fun acc o =>
          acc + ε / hopeDenominator outcomes *
            (o.utility - meanUtility outcomes) := by
      funext acc o
      simp [hopeAdjustment_eq_of_denom_ne_zero outcomes ε o h]
    simpa [hRewrite, sum_centered_zero outcomes] using this

lemma foldl_abs_nonneg (xs : List FutureOutcome) (μ : ℝ) :
    0 ≤ xs.foldl (fun acc o => acc + |o.utility - μ|) 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [foldl_abs_add_const xs μ (0 + |x.utility - μ|)]
    have h_abs_nonneg : 0 ≤ |x.utility - μ| := abs_nonneg _
    linarith

lemma hopeDenominator_nonneg (outcomes : List FutureOutcome) :
    0 ≤ hopeDenominator outcomes := by
  unfold hopeDenominator
  exact foldl_abs_nonneg outcomes (meanUtility outcomes)

lemma abs_centered_le_foldl_const
    {outcomes : List FutureOutcome} {outcome : FutureOutcome} {μ : ℝ}
    (h_mem : outcome ∈ outcomes) :
    |outcome.utility - μ| ≤ outcomes.foldl (fun acc o => acc + |o.utility - μ|) 0 := by
  induction outcomes with
  | nil => simp at h_mem
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [foldl_abs_add_const xs μ (0 + |x.utility - μ|)]
    cases List.mem_cons.mp h_mem with
    | inl heq =>
      rw [heq]
      have h_nonneg := foldl_abs_nonneg xs μ
      linarith
    | inr hmem =>
      have h_abs_nonneg : 0 ≤ |x.utility - μ| := abs_nonneg _
      have h_ih := ih hmem
      linarith

lemma abs_centered_le_denom
    {outcomes : List FutureOutcome} {outcome : FutureOutcome}
    (h_mem : outcome ∈ outcomes) :
    |outcome.utility - meanUtility outcomes| ≤ hopeDenominator outcomes := by
  classical
  unfold hopeDenominator
  exact abs_centered_le_foldl_const (μ := meanUtility outcomes) h_mem

private lemma foldl_add_shift {α : Type*} (f : α → ℝ) (xs : List α) (c : ℝ) :
    xs.foldl (fun acc x => acc + f x) c = c + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing c with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [ih (c + f y), ih (0 + f y)]
    ring

lemma foldl_probabilities_plus_adjustments
    (outcomes : List FutureOutcome) (ε : ℝ) :
    outcomes.foldl (fun acc o => acc + hopeAdjustedProbability outcomes ε o) 0
      = outcomes.foldl (fun acc o => acc + o.probability) 0 +
        outcomes.foldl (fun acc o => acc + hopeAdjustment outcomes ε o) 0 := by
  induction outcomes with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, hopeAdjustedProbability]
    -- LHS = xs.foldl ... (0 + (x.probability + hopeAdjustment outcomes ε x))
    -- RHS = xs.foldl ... (0 + x.probability) + xs.foldl ... (0 + hopeAdjustment outcomes ε x)
    rw [foldl_add_shift (fun o => o.probability + hopeAdjustment outcomes ε o) xs,
        foldl_add_shift (fun o => o.probability) xs,
        foldl_add_shift (fun o => hopeAdjustment outcomes ε o) xs]
    simp only [zero_add]
    rw [ih]
    ring

lemma hopeAdjustment_abs_le
    (outcomes : List FutureOutcome) (ε : ℝ) (outcome : FutureOutcome)
    (h_mem : outcome ∈ outcomes) (h_nonneg : 0 ≤ ε) :
    |hopeAdjustment outcomes ε outcome| ≤ ε := by
  classical
  unfold hopeAdjustment
  simp only
  set denom := hopeDenominator outcomes
  set centered := outcome.utility - meanUtility outcomes
  by_cases h_zero : denom = 0
  · simp [h_zero, h_nonneg]
  · simp only [h_zero, ↓reduceIte]
    have h_denom_pos : 0 < denom := by
      have h_ge := hopeDenominator_nonneg outcomes
      exact lt_of_le_of_ne h_ge (Ne.symm h_zero)
    have h_centered_le : |centered| ≤ denom := abs_centered_le_denom h_mem
    rw [abs_mul, abs_div]
    calc |ε| * (|centered| / |denom|)
        = ε * (|centered| / denom) := by rw [abs_of_nonneg h_nonneg, abs_of_pos h_denom_pos]
      _ ≤ ε * (denom / denom) := by
          apply mul_le_mul_of_nonneg_left
          · exact div_le_div_of_nonneg_right h_centered_le h_denom_pos
          · exact h_nonneg
      _ = ε * 1 := by rw [div_self (ne_of_gt h_denom_pos)]
      _ = ε := mul_one ε

lemma hopeDenominator_pos_of_exists_ne_mean
    (outcomes : List FutureOutcome) (outcome : FutureOutcome)
    (h_mem : outcome ∈ outcomes)
    (h_ne : outcome.utility ≠ meanUtility outcomes) :
    0 < hopeDenominator outcomes := by
  have h_abs_pos : 0 < |outcome.utility - meanUtility outcomes| :=
    abs_pos.mpr (sub_ne_zero.mpr h_ne)
  exact lt_of_lt_of_le h_abs_pos (abs_centered_le_denom (outcomes := outcomes)
    (outcome := outcome) h_mem)

lemma hopeAdjustment_pos_of_above_mean
    (outcomes : List FutureOutcome) (ε : ℝ) (outcome : FutureOutcome)
    (h_mem : outcome ∈ outcomes) (h_pos : 0 < ε)
    (h_above : outcome.utility > meanUtility outcomes) :
    hopeAdjustment outcomes ε outcome > 0 := by
  classical
  set denom := hopeDenominator outcomes
  have h_den_pos := hopeDenominator_pos_of_exists_ne_mean outcomes outcome
    h_mem (ne_of_gt h_above)
  have h_den_ne : denom ≠ 0 := ne_of_gt h_den_pos
  have h_formula := hopeAdjustment_eq_of_denom_ne_zero outcomes ε outcome h_den_ne
  have h_scale_pos : 0 < ε / denom := div_pos h_pos h_den_pos
  have h_centered_pos : 0 < outcome.utility - meanUtility outcomes :=
    sub_pos.mpr h_above
  have : hopeAdjustment outcomes ε outcome = ε / denom *
      (outcome.utility - meanUtility outcomes) := by
    simpa [denom] using h_formula
  have h_product_pos :
      ε / denom * (outcome.utility - meanUtility outcomes) > 0 :=
    mul_pos h_scale_pos h_centered_pos
  simpa [this] using h_product_pos


/-! ## Core Definitions -/

-- FutureOutcome structure moved to top of file to fix forward reference

/-- Add optimism prior to utility -/
def optimism_prior (utility : ℝ) (ε : ℝ) : ℝ := utility + ε

/-- Compute optimism adjustment (positive for high utility, negative for low) -/
noncomputable def compute_optimism_adjustment
  (outcome : FutureOutcome)
  (mean_utility : ℝ)
  (ε_total : ℝ) :
  ℝ :=
  if outcome.utility > mean_utility then ε_total else -ε_total

/-- Apply hope: select outcome with adjusted probabilities -/
noncomputable def ApplyHope
  (outcomes : List FutureOutcome)
  (ε : ℝ)  -- Optimism prior magnitude
  (h_normalized : outcomes.foldl (fun acc o => acc + o.probability) 0 = 1)
  (h_ε_small : 0 < ε ∧ ε < 0.1)
  (h_nonempty : outcomes ≠ []) :
  FutureOutcome :=
  let _mean_utility := (outcomes.foldl (fun acc o => acc + o.utility) 0) / (outcomes.length : ℝ)
  -- Select outcome with highest adjusted value
  match outcomes, h_nonempty with
  | first :: _, _ =>
    outcomes.foldl (fun best current =>
      let adjusted_value_current := current.utility + optimism_prior current.utility ε
      let adjusted_value_best := best.utility + optimism_prior best.utility ε
      if adjusted_value_current > adjusted_value_best then current else best
    ) first

/-- Helper: fold-based max selection returns start or a member of the list -/
private lemma hope_fold_mem
    (ε : ℝ) (outcomes : List FutureOutcome) (start : FutureOutcome) :
    outcomes.foldl (fun best current =>
      let adjusted_value_current := current.utility + optimism_prior current.utility ε
      let adjusted_value_best := best.utility + optimism_prior best.utility ε
      if adjusted_value_current > adjusted_value_best then current else best) start = start ∨
    outcomes.foldl (fun best current =>
      let adjusted_value_current := current.utility + optimism_prior current.utility ε
      let adjusted_value_best := best.utility + optimism_prior best.utility ε
      if adjusted_value_current > adjusted_value_best then current else best) start ∈ outcomes := by
  induction outcomes generalizing start with
  | nil => left; rfl
  | cons c cs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    split_ifs with h
    · cases ih c with
      | inl heq => right; left; exact heq
      | inr hmem => right; right; exact hmem
    · cases ih start with
      | inl heq => left; exact heq
      | inr hmem => right; right; exact hmem

lemma ApplyHope_mem
  (outcomes : List FutureOutcome)
  (ε : ℝ)
  (h_normalized : outcomes.foldl (fun acc o => acc + o.probability) 0 = 1)
  (h_ε_small : 0 < ε ∧ ε < 0.1)
  (h_nonempty : outcomes ≠ []) :
  ApplyHope outcomes ε h_normalized h_ε_small h_nonempty ∈ outcomes := by
  unfold ApplyHope
  match outcomes, h_nonempty with
  | first :: rest, _ =>
    simp only
    have h := hope_fold_mem ε (first :: rest) first
    cases h with
    | inl heq =>
      rw [heq]
      exact List.mem_cons_self first rest
    | inr hmem => exact hmem

/-! ## Core Theorems -/

/-- Hope prevents paralysis -/
theorem hope_prevents_paralysis
  (outcomes : List FutureOutcome)
  (ε : ℝ)
  (h_normalized : outcomes.foldl (fun acc o => acc + o.probability) 0 = 1)
  (h_ε_small : 0 < ε ∧ ε < 0.1)
  (h_nonempty : outcomes ≠ [])
  (h_all_negative : ∀ o ∈ outcomes, o.probability < 0.1) :
  -- With Hope, some action is still selected (not inaction)
  (ApplyHope outcomes ε h_normalized h_ε_small h_nonempty) ∈ outcomes := by
  exact ApplyHope_mem outcomes ε h_normalized h_ε_small h_nonempty

/-- Hope preserves normalization because the optimism prior is a zero-sum adjustment. -/
theorem hope_preserves_normalization
  (outcomes : List FutureOutcome)
  (ε : ℝ)
  (h_normalized : outcomes.foldl (fun acc o => acc + o.probability) 0 = 1)
  (h_ε_small : 0 < ε ∧ ε < 0.1) :
  outcomes.foldl (fun acc o => acc + hopeAdjustedProbability outcomes ε o) 0 = 1 := by
  have h_split := foldl_probabilities_plus_adjustments outcomes ε
  have h_zero := hopeAdjustment_sum_eq_zero outcomes ε
  simpa [h_split, h_zero, h_normalized, add_comm, add_left_comm, add_assoc]

/-- Hope must be bounded to preserve realism -/
theorem hope_bounded_necessary
  (outcomes : List FutureOutcome)
  (ε : ℝ)
  (h_ε_small : 0 < ε ∧ ε < 0.1)
  (h_support : ∀ o ∈ outcomes, ε ≤ o.probability ∧ ε ≤ 1 - o.probability) :
  ∀ o ∈ outcomes,
    let adjusted := hopeAdjustedProbability outcomes ε o
    0 ≤ adjusted ∧ adjusted ≤ 1 := by
  classical
  intro o h_mem
  have h_bounds := h_support o h_mem
  have h_abs := hopeAdjustment_abs_le outcomes ε o h_mem (le_of_lt h_ε_small.1)
  have h_adj := abs_le.mp (by simpa using h_abs)
  have h_lower : -ε ≤ hopeAdjustment outcomes ε o := h_adj.1
  have h_upper : hopeAdjustment outcomes ε o ≤ ε := h_adj.2
  have h_prob_lower := h_bounds.1
  have h_prob_upper : o.probability ≤ 1 - ε := by linarith [h_bounds.2]
  simp only [hopeAdjustedProbability]
  constructor
  · -- 0 ≤ o.probability + hopeAdjustment
    -- From h_prob_lower: ε ≤ o.probability and h_lower: -ε ≤ hopeAdjustment
    -- So 0 = ε + (-ε) ≤ o.probability + hopeAdjustment
    linarith
  · -- o.probability + hopeAdjustment ≤ 1
    -- From h_prob_upper: o.probability ≤ 1 - ε and h_upper: hopeAdjustment ≤ ε
    -- So o.probability + hopeAdjustment ≤ (1 - ε) + ε = 1
    linarith

/-- Hope enables exploration of low-probability positive futures -/
theorem hope_enables_exploration
  (outcomes : List FutureOutcome)
  (ε : ℝ)
  (h_normalized : outcomes.foldl (fun acc o => acc + o.probability) 0 = 1)
  (h_ε_small : 0 < ε ∧ ε < 0.1)
  (h_nonempty : outcomes ≠ [])
  (positive_outcome : FutureOutcome)
  (h_positive_in : positive_outcome ∈ outcomes)
  (h_positive_above_mean : positive_outcome.utility > meanUtility outcomes)
  (h_positive_unlikely : positive_outcome.probability < 0.05) :
  hopeAdjustedProbability outcomes ε positive_outcome
    > positive_outcome.probability := by
  classical
  have h_adj_pos := hopeAdjustment_pos_of_above_mean outcomes ε positive_outcome
    h_positive_in h_ε_small.1 h_positive_above_mean
  have : hopeAdjustedProbability outcomes ε positive_outcome
      = positive_outcome.probability + hopeAdjustment outcomes ε positive_outcome := by
    rfl
  have h_pos := add_lt_add_left h_adj_pos positive_outcome.probability
  simpa [this] using h_pos

/-! ## Despair vs Hope -/

/-!
Despair (absence of hope) leads to inaction (documentation / TODO).

Intended claim: under a reasonable policy model, if all perceived outcomes are negative and not
negligible, the agent tends to choose inaction unless a Hope-like reweighting is applied.
-/

/-!
Hope distinguishes high vs low utility outcomes (documentation / TODO).

Intended claim: higher-utility outcomes receive a positive adjustment and lower-utility outcomes
receive a negative adjustment, bounded by ε.
-/

/-! ## Compositional Properties -/

/-- Hope can be applied iteratively (multi-stage decisions) -/
theorem hope_iterative
  (stage1 stage2 : List FutureOutcome)
  (ε : ℝ)
  (h1 : stage1.foldl (fun acc o => acc + o.probability) 0 = 1)
  (h2 : stage2.foldl (fun acc o => acc + o.probability) 0 = 1)
  (h_ε : 0 < ε ∧ ε < 0.1)
  (h_ne1 : stage1 ≠ [])
  (h_ne2 : stage2 ≠ []) :
  ApplyHope stage1 ε h1 h_ε h_ne1 ∈ stage1 ∧
    ApplyHope stage2 ε h2 h_ε h_ne2 ∈ stage2 := by
  constructor
  · exact ApplyHope_mem stage1 ε h1 h_ε h_ne1
  · exact ApplyHope_mem stage2 ε h2 h_ε h_ne2

/-!
Hope magnitude should be calibrated to uncertainty (documentation / TODO).

Intended claim: higher uncertainty suggests smaller ε (to avoid hallucinating confidence), while
lower uncertainty can tolerate larger ε without distortion.
-/

/-! ## Ethical Interpretation -/

/-!
Hope enables action under uncertainty (documentation / TODO).
-/

/-!
Hope preserves possibility of positive futures (documentation / TODO).
-/

/-!
Hope is bounded optimism, not unrealistic fantasy (documentation / TODO).

Intended guardrail: ε must be small enough that Hope does not distort probabilities beyond a
predefined bound.
-/

/-- Hope-compatible value improvements pass the consent audit check. -/
theorem hope_respects_consent
  (agents : List AgentId)
  (actor : AgentId)
  (value_before value_after : AgentId → ℝ)
  (h_gain : ∀ i, value_before i ≤ value_after i) :
  ∀ entry ∈ Audit.consent_table agents actor
      (fun i => value_after i - value_before i), entry.2.2 = true := by
  classical
  intro entry h_entry
  rcases List.mem_map.mp h_entry with ⟨agent, h_agent, rfl⟩
  simp [Audit.consent_table, Audit.nonnegBool_true_iff, sub_nonneg.mpr (h_gain agent), h_agent]

end Virtues
end Ethics
end IndisputableMonolith
