import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Wisdom

/-!
# Prudence: Variance-Adjusted Wisdom

Prudence extends Wisdom by incorporating risk-aversion, minimizing both expected
skew and variance to ensure robust long-term decisions.

## Mathematical Definition

Value(S) := E[|σ_future|] + lambda_val · Var(|σ_future|)

where lambda_val is risk-aversion parameter (higher lambda_val → more conservative).

## Physical Grounding

- **Extends Wisdom**: Adds variance term to φ-discounted expectation
- **Risk-aversion**: Penalizes unpredictable outcomes
- **Robustness**: Less susceptible to shocks

## Connection to virtues.tex

Section 7 (Prudence): "To make decisions that minimize future risk and uncertainty.
While Wisdom optimizes for the best expected outcome, Prudence optimizes for the
most reliable outcome by minimizing variance."

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState
open scoped Classical

noncomputable section

/-! ## Core Definitions -/

/-- Variance estimate for a moral state using squared bond strains. -/
noncomputable def variance_estimate (s : MoralState) : ℝ :=
  s.ledger.active_bonds.sum fun b =>
    (s.ledger.bond_multipliers b - 1) ^ 2

/-- The variance estimate is always non-negative. -/
lemma variance_estimate_nonneg (s : MoralState) : 0 ≤ variance_estimate s := by
  classical
  unfold variance_estimate
  refine Finset.sum_nonneg ?_
  intro b hb
  exact sq_nonneg _

/-- Risk-adjusted value: expected skew + risk penalty -/
noncomputable def risk_adjusted_value (s : MoralState) (lambda_val : ℝ) : ℝ :=
  (Int.natAbs s.skew : ℝ) + lambda_val * variance_estimate s

/-- Selection step used by `PrudentChoice`. -/
private def prudenceStep (lambda_val : ℝ) (best current : MoralState) : MoralState :=
  if risk_adjusted_value current lambda_val < risk_adjusted_value best lambda_val then current else best

/-- Prudent choice: select option minimizing risk-adjusted value.

This definition permits `lambda_val = 0`, enabling direct comparison with
`WiseChoice` (pure expectation minimization) for compatibility proofs. The
semantic requirement `0 < lambda_val` is enforced where needed rather than in the core
definition.
-/
noncomputable def PrudentChoice
  (s : MoralState)
  (choices : List MoralState)
  (lambda_val : ℝ) :
  MoralState :=
  choices.foldl (prudenceStep lambda_val) s

/-- Folding helper: the accumulated choice never has higher score than any processed element. -/
private lemma prudence_fold_step_min
    (lambda_val : ℝ) (choices : List MoralState) (start : MoralState) :
    risk_adjusted_value (choices.foldl (prudenceStep lambda_val) start) lambda_val ≤ risk_adjusted_value start lambda_val ∧
      ∀ c ∈ choices,
        risk_adjusted_value (choices.foldl (prudenceStep lambda_val) start) lambda_val ≤ risk_adjusted_value c lambda_val := by
  induction choices generalizing start with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    unfold prudenceStep at *
    split_ifs with h
    · have ⟨h1, h2⟩ := ih c
      constructor
      · exact le_trans h1 (le_of_lt h)
      · intro x hx
        cases hx with
        | inl heq => rw [heq]; exact h1
        | inr hmem => exact h2 x hmem
    · have ⟨h1, h2⟩ := ih start
      constructor
      · exact h1
      · intro x hx
        cases hx with
        | inl heq => rw [heq]; exact le_trans h1 (le_of_not_lt h)
        | inr hmem => exact h2 x hmem

/-- The fold-based chooser always returns an element from the processed list. -/
private lemma prudence_fold_mem
    (lambda_val : ℝ) (choices : List MoralState) (start : MoralState) :
    choices.foldl (prudenceStep lambda_val) start = start ∨
      choices.foldl (prudenceStep lambda_val) start ∈ choices := by
  induction choices generalizing start with
  | nil => left; rfl
  | cons c cs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    unfold prudenceStep
    split_ifs with h
    · cases ih c with
      | inl heq => right; left; exact heq
      | inr hmem => right; right; exact hmem
    · cases ih start with
      | inl heq => left; exact heq
      | inr hmem => right; right; exact hmem

/-! ## Core Theorems -/

/-- Prudence extends Wisdom (lambda_val=0 case recovers Wisdom) -/
theorem prudence_extends_wisdom
  (s : MoralState)
  (choices : List MoralState) :
  -- When lambda_val=0, prudence reduces to wisdom (no risk penalty)
  ∀ c ∈ choices, risk_adjusted_value c 0 = (Int.natAbs c.skew : ℝ) := by
  intro c _
  unfold risk_adjusted_value
  simp

/-- With zero risk penalty, Prudence selects the smaller of
`s` and the wisdom-optimal choice by skew magnitude.

PrudentChoice@0 minimizes risk_adjusted_value = |skew| over {s} ∪ choices.
WiseChoice minimizes wisdomScore = |skew| × constant over choices.
Since both minimize |skew|, they agree on the minimum element of choices. -/
theorem prudence_zero_lambda_skew_min
  (s : MoralState)
  (choices : List MoralState)
  (h_nonempty : choices ≠ []) :
  let prudent := PrudentChoice s choices 0
  let wise := WiseChoice s choices
  (Int.natAbs prudent.skew : ℝ) =
    min ((Int.natAbs s.skew : ℝ)) (Int.natAbs wise.skew : ℝ) := by
  simp only
  have h_rav_eq : ∀ m : MoralState, risk_adjusted_value m 0 = (Int.natAbs m.skew : ℝ) := by
    intro m; simp [risk_adjusted_value]
  have ⟨hle_s, hle_choices⟩ := prudence_fold_step_min 0 choices s
  have h_pru_mem := prudence_fold_mem 0 choices s
  have h_wise_mem := IndisputableMonolith.Ethics.Virtues.wisdom_returns_valid_choice s choices
  simp only [h_rav_eq] at hle_s hle_choices
  cases h_pru_mem with
  | inl h_pru_eq_s =>
    simp only [h_pru_eq_s]
    cases h_wise_mem with
    | inl h_wise_eq_s => simp only [h_wise_eq_s, min_self]
    | inr h_wise_in_choices =>
      have h_s_le_wise := hle_choices _ h_wise_in_choices
      simp only [min_eq_left h_s_le_wise]
  | inr h_pru_in_choices =>
    cases h_wise_mem with
    | inl h_wise_eq_s => simp only [h_wise_eq_s, min_eq_right hle_s]
    | inr h_wise_in_choices =>
      have h_pru_le_wise := hle_choices _ h_wise_in_choices
      have h_wise_le_pru := IndisputableMonolith.Ethics.Virtues.wisdom_minimizes_skew_natAbs
        s choices h_nonempty (PrudentChoice s choices 0) h_pru_in_choices
      have h_eq := le_antisymm h_pru_le_wise h_wise_le_pru
      simp only [h_eq, min_eq_right hle_s]

/-- Prudence minimizes the risk-adjusted value across the available choices. -/
theorem prudence_reduces_volatility
  (s : MoralState)
  (choices : List MoralState)
  (lambda_val : ℝ)
  (h_lambda : 0 < lambda_val) :
  let result := PrudentChoice s choices lambda_val
  ∀ c ∈ s :: choices, risk_adjusted_value result lambda_val ≤ risk_adjusted_value c lambda_val := by
  simp only
  intro c hc
  unfold PrudentChoice
  have ⟨h1, h2⟩ := prudence_fold_step_min lambda_val choices s
  cases List.mem_cons.mp hc with
  | inl heq => rw [heq]; exact h1
  | inr hmem => exact h2 c hmem

/-- The risk-adjusted value grows monotonically with lambda_val. -/
theorem prudence_lambda_monotonic
  (s : MoralState)
  (lambda_val₁ lambda_val₂ : ℝ)
  (h_order : lambda_val₁ ≤ lambda_val₂) :
  risk_adjusted_value s lambda_val₁ ≤ risk_adjusted_value s lambda_val₂ := by
  unfold risk_adjusted_value
  have hv := variance_estimate_nonneg s
  calc (Int.natAbs s.skew : ℝ) + lambda_val₁ * variance_estimate s
      ≤ (Int.natAbs s.skew : ℝ) + lambda_val₂ * variance_estimate s := by
        apply add_le_add_left
        exact mul_le_mul_of_nonneg_right h_order hv

/-! ## Ethical Properties -/

/-- Prudence prefers lower variance when skews are equal. -/
theorem prudence_prefers_stability
  (s : MoralState)
  (risky stable : MoralState)
  (lambda_val : ℝ)
  (h_lambda : 0 < lambda_val)
  (h_skew : risky.skew = stable.skew)
  (h_var : variance_estimate stable < variance_estimate risky)
  (h_stable_beats_s : risk_adjusted_value stable lambda_val < risk_adjusted_value s lambda_val) :
  PrudentChoice s [risky, stable] lambda_val = stable := by
  -- PrudentChoice s [risky, stable] = foldl prudenceStep s [risky, stable]
  -- = prudenceStep (prudenceStep s risky) stable
  simp only [PrudentChoice, List.foldl_cons, List.foldl_nil]
  -- Need: prudenceStep (prudenceStep s risky) stable = stable
  -- This requires: risk_adjusted_value stable < risk_adjusted_value (prudenceStep s risky)
  -- First show: risk_adjusted_value stable < risk_adjusted_value risky
  have h_stable_beats_risky : risk_adjusted_value stable lambda_val < risk_adjusted_value risky lambda_val := by
    unfold risk_adjusted_value
    rw [h_skew]
    have h := mul_lt_mul_of_pos_left h_var h_lambda
    linarith
  -- Now: prudenceStep s risky is either s or risky (depending on which has lower value)
  unfold prudenceStep
  split_ifs with h1 h2
  · -- prudenceStep s risky = risky (risky < s)
    -- Need: stable < risky, which we have
    simp [h_stable_beats_risky]
  · -- prudenceStep s risky = s (s ≤ risky)
    -- Need: stable < s, which is h_stable_beats_s
    simp [h_stable_beats_s]

/-- Prudence tolerates higher skew if variance reduction compensates.

    This theorem compares two options:
    - Option A (high_skew = low_var): higher |skew| but lower variance
    - Option B (low_skew = high_var): lower |skew| but higher variance

    When λ × (variance gap) > (skew gap), Option A wins because its
    risk_adjusted_value is lower despite higher skew.

    Note: The original statement has ambiguous parameters. A cleaner formulation would
    use just two MoralStates (optionA and optionB) with explicit constraints. -/
/-- Prudence tolerates higher skew if variance reduction compensates.

    Comparing `safe` (high skew, low variance) vs `risky` (low skew, high variance).
    If λ is large enough, `safe` is preferred despite higher skew. -/
theorem prudence_tradeoff
  (s : MoralState)
  (safe risky : MoralState)
  (lambda_val : ℝ)
  (h_lambda : 0 < lambda_val)
  -- safe has higher skew than risky
  (h_skew_order : (Int.natAbs risky.skew : ℝ) < (Int.natAbs safe.skew : ℝ))
  -- safe has lower variance than risky
  (h_var_order : variance_estimate safe < variance_estimate risky)
  -- safe beats s (otherwise we might stick with s)
  (h_beats_s : risk_adjusted_value safe lambda_val < risk_adjusted_value s lambda_val) :
  -- If the variance gap times lambda exceeds the skew gap...
  lambda_val * (variance_estimate risky - variance_estimate safe) >
    ((Int.natAbs safe.skew : ℝ) - (Int.natAbs risky.skew : ℝ)) →
  -- ...then safe is chosen
  PrudentChoice s [safe, risky] lambda_val = safe := by
  intro h_tradeoff
  -- Strategy: Calculate risk_adjusted_value for both
  -- Show val(safe) < val(risky) using the tradeoff inequality
  -- Then simulate the fold
  have h_safe_beats_risky : risk_adjusted_value safe lambda_val < risk_adjusted_value risky lambda_val := by
    unfold risk_adjusted_value
    -- val(safe) < val(risky)
    -- skew(safe) + λ*var(safe) < skew(risky) + λ*var(risky)
    -- skew(safe) - skew(risky) < λ*var(risky) - λ*var(safe)
    -- skew(safe) - skew(risky) < λ*(var(risky) - var(safe))
    linarith

  simp only [PrudentChoice, List.foldl_cons, List.foldl_nil]
  unfold prudenceStep
  -- Step 1: compare s and safe
  -- if val(safe) < val(s) then safe else s
  -- We have h_beats_s : val(safe) < val(s)
  split_ifs with h1
  · -- Current best is safe
    -- Step 2: compare safe and risky
    -- if val(risky) < val(safe) then risky else safe
    -- We have val(safe) < val(risky), so NOT (val(risky) < val(safe))
    split_ifs with h2
    · -- Impossible: val(risky) < val(safe) contradicts h_safe_beats_risky
      linarith
    · -- Result is safe
      rfl
  · -- h1 is false: val(safe) ≥ val(s)
    -- Contradicts h_beats_s
    linarith

/-- Prudence returns a valid choice (or fallback). -/
theorem prudence_returns_valid
  (s : MoralState)
  (choices : List MoralState)
  (lambda_val : ℝ) :
  let result := PrudentChoice s choices lambda_val
  result = s ∨ result ∈ choices := by
  simp only
  unfold PrudentChoice
  exact prudence_fold_mem lambda_val choices s

/-! ## Consistency -/

/-- Helper: if start has minimum value among start :: choices, fold returns start -/
private lemma prudence_fold_min_returns_start
    (lambda_val : ℝ) (choices : List MoralState) (start : MoralState)
    (h_min : ∀ c ∈ choices, risk_adjusted_value start lambda_val ≤ risk_adjusted_value c lambda_val) :
    choices.foldl (prudenceStep lambda_val) start = start := by
  induction choices generalizing start with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    unfold prudenceStep
    have h_c := h_min c (List.mem_cons.mpr (Or.inl rfl))
    simp only [not_lt.mpr h_c, ↓reduceIte]
    apply ih
    intro x hx
    exact h_min x (List.mem_cons.mpr (Or.inr hx))

/-- Prudence is idempotent (applying twice yields same result). -/
theorem prudence_idempotent
  (s : MoralState)
  (choices : List MoralState)
  (lambda_val : ℝ) :
  let result := PrudentChoice s choices lambda_val
  PrudentChoice result choices lambda_val = result := by
  simp only
  unfold PrudentChoice
  -- result = choices.foldl (prudenceStep lambda_val) s has minimum value among s :: choices
  have ⟨_, h_min_choices⟩ := prudence_fold_step_min lambda_val choices s
  exact prudence_fold_min_returns_start lambda_val choices _ h_min_choices

/-- Helper: foldl min over permuted lists gives the same result -/
private lemma foldl_min_perm {α : Type*} [LinearOrder α] (l₁ l₂ : List α) (h : l₁.Perm l₂) (init : α) :
    l₁.foldl min init = l₂.foldl min init := by
  induction h generalizing init with
  | nil => rfl
  | cons x _ ih => simp only [List.foldl_cons]; exact ih (min init x)
  | swap x y l =>
    simp only [List.foldl_cons]
    -- Goal: l.foldl min (min (min init x) y) = l.foldl min (min (min init y) x)
    -- Both equal l.foldl min (min init (min x y)) by associativity and commutativity
    congr 1
    -- Need: min (min init x) y = min (min init y) x
    -- Both equal min init (min x y)
    rw [min_assoc, min_assoc, min_comm x y]
  | trans _ _ ih1 ih2 => exact (ih1 init).trans (ih2 init)

/-- Helper: foldl min init ≤ init -/
private lemma foldl_min_le_init {α : Type*} [LinearOrder α] (l : List α) (init : α) :
    l.foldl min init ≤ init := by
  induction l generalizing init with
  | nil => exact le_refl _
  | cons x xs ih =>
    simp only [List.foldl_cons]
    calc xs.foldl min (min init x) ≤ min init x := ih (min init x)
       _ ≤ init := min_le_left _ _

/-- Helper: foldl min absorbs elements from the list -/
private lemma foldl_min_le_mem {α : Type*} [LinearOrder α] (l : List α) (init : α) (x : α) (hx : x ∈ l) :
    l.foldl min init ≤ x := by
  induction l generalizing init x with
  | nil => nomatch hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with heq | hx'
    · -- x = y, need to show ys.foldl min (min init y) ≤ y
      subst heq
      have h1 : ys.foldl min (min init x) ≤ min init x := foldl_min_le_init ys (min init x)
      exact le_trans h1 (min_le_right init x)
    · exact ih (min init y) x hx'

/-- Helper: fold result is either init or some element of the list -/
private lemma foldl_min_mem_or_init {α : Type*} [LinearOrder α] (l : List α) (init : α) :
    l.foldl min init = init ∨ l.foldl min init ∈ l := by
  induction l generalizing init with
  | nil => left; rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases ih (min init x) with h | h
    · -- xs.foldl min (min init x) = min init x
      rw [h]
      by_cases hix : init ≤ x
      · -- min init x = init
        left; exact min_eq_left hix
      · -- min init x = x
        push_neg at hix
        right
        rw [min_eq_right (le_of_lt hix)]
        exact List.mem_cons.mpr (Or.inl rfl)
    · -- xs.foldl min (min init x) ∈ xs
      right; exact List.mem_cons_of_mem x h

/-- foldl min with different init values from the list gives the same result -/
private lemma foldl_min_init_mem {α : Type*} [LinearOrder α] (l : List α) (a b : α) (ha : a ∈ l) (hb : b ∈ l) :
    l.foldl min a = l.foldl min b := by
  -- Both compute the minimum of the list (since a, b ∈ l)
  -- Key insight: foldl min a ≤ every element of l, and the result is either a or in l
  -- When a ∈ l, the result is in l, so foldl min b ≤ result ≤ foldl min b
  apply le_antisymm
  · -- l.foldl min a ≤ l.foldl min b
    -- The result of foldl min b is either b or some c ∈ l
    -- In either case, foldl min a ≤ that element (by foldl_min_le_mem or since b ∈ l)
    rcases foldl_min_mem_or_init l b with h | h
    · rw [h]; exact foldl_min_le_mem l a b hb
    · exact foldl_min_le_mem l a _ h
  · -- Symmetric
    rcases foldl_min_mem_or_init l a with h | h
    · rw [h]; exact foldl_min_le_mem l b a ha
    · exact foldl_min_le_mem l b _ h


/-- The fold achieves minimum risk_adjusted_value in the list -/
private lemma prudence_fold_achieves_min
    (lambda_val : ℝ) (c : MoralState) (cs : List MoralState) :
    risk_adjusted_value (cs.foldl (prudenceStep lambda_val) c) lambda_val =
      cs.foldl (fun acc m => min acc (risk_adjusted_value m lambda_val)) (risk_adjusted_value c lambda_val) := by
  induction cs generalizing c with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    -- LHS: risk_adjusted_value (xs.foldl (prudenceStep lambda_val) (prudenceStep lambda_val c x)) lambda_val
    -- RHS: xs.foldl f (min (r c) (r x))
    -- prudenceStep lambda_val c x = if (r x) < (r c) then x else c
    by_cases h : risk_adjusted_value x lambda_val < risk_adjusted_value c lambda_val
    · -- x has lower value, so prudenceStep returns x
      have hstep : prudenceStep lambda_val c x = x := by unfold prudenceStep; simp [h]
      rw [hstep]
      simp only [min_eq_right (le_of_lt h)]
      exact ih x
    · -- c has lower or equal value, so prudenceStep returns c
      have hstep : prudenceStep lambda_val c x = c := by unfold prudenceStep; simp [h]
      rw [hstep]
      simp only [min_eq_left (not_lt.mp h)]
      exact ih c

/-- Prudence is stable under permutation of choices. -/
theorem prudence_permutation_invariant
  (s : MoralState)
  (choices₁ choices₂ : List MoralState)
  (lambda_val : ℝ)
  (h_perm : choices₁.Perm choices₂) :
  risk_adjusted_value (PrudentChoice s choices₁ lambda_val) lambda_val =
    risk_adjusted_value (PrudentChoice s choices₂ lambda_val) lambda_val := by
  -- Both folds achieve the minimum risk_adjusted_value
  -- Since the lists are permutations, they have the same minimum
  simp only [PrudentChoice]
  cases choices₁ with
  | nil =>
    -- h_perm : [].Perm choices₂
    -- Need to show choices₂ = []
    simp only [List.Perm.nil_eq h_perm]
  | cons c₁ cs₁ =>
    cases choices₂ with
    | nil =>
      exfalso
      have : (c₁ :: cs₁).length = [].length := h_perm.length_eq
      simp at this
    | cons c₂ cs₂ =>
      -- Both folds achieve the minimum value over {s} ∪ choices
      -- Use prudence_fold_achieves_min to convert to foldl min
      rw [prudence_fold_achieves_min, prudence_fold_achieves_min]
      -- Now we have foldl (fun acc m => min acc (r m)) init on both sides
      -- The mapped lists are permutations, so the min values are equal
      -- Key: foldl (fun acc m => min acc (f m)) init l = foldl min init (l.map f)
      have foldl_map_eq : ∀ (l : List MoralState) (init : ℝ),
          l.foldl (fun acc m => min acc (risk_adjusted_value m lambda_val)) init =
          (l.map (fun m => risk_adjusted_value m lambda_val)).foldl min init := by
        intro l init
        induction l generalizing init with
        | nil => rfl
        | cons x xs ih =>
          simp only [List.foldl_cons, List.map_cons]
          exact ih (min init (risk_adjusted_value x lambda_val))
      rw [foldl_map_eq, foldl_map_eq]
      exact foldl_min_perm _ _ (h_perm.map _) (risk_adjusted_value s lambda_val)

/-!
### Outstanding integration work

* Bridge `variance_estimate` to `Harm.ValueTypes.Variance` once accessible.
* Validate `lambda_val` ranges against physical constants (is there a canonical risk aversion?).
-/

-- end Virtues
-- end Ethics
-- end IndisputableMonolith
