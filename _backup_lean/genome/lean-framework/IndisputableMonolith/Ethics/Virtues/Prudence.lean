import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Wisdom

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
  intro b _
  exact sq_nonneg _

/-- Risk-adjusted value: expected skew + risk penalty -/
noncomputable def risk_adjusted_value (s : MoralState) (lambda_val : ℝ) : ℝ :=
  (abs s.skew : ℝ) + lambda_val * variance_estimate s

/-- Selection step used by `PrudentChoice`. -/
private def prudenceStep (lambda_val : ℝ) (best current : MoralState) : MoralState :=
  if risk_adjusted_value current lambda_val < risk_adjusted_value best lambda_val then current else best

/-- Prudent choice: select option minimizing risk-adjusted value. -/
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
        | inl heq => rw [heq]; exact le_trans h1 (le_of_not_gt h)
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
    split_ifs with _
    · cases ih c with
      | inl heq => right; left; exact heq
      | inr hmem => right; right; exact hmem
    · cases ih start with
      | inl heq => left; exact heq
      | inr hmem => right; right; exact hmem

/-! ## Core Theorems -/

/-- Prudence extends Wisdom (lambda_val=0 case recovers Wisdom) -/
theorem prudence_extends_wisdom
  (choices : List MoralState) :
  ∀ c ∈ choices, risk_adjusted_value c 0 = (abs c.skew : ℝ) := by
  intro c _
  unfold risk_adjusted_value
  simp

/-- The fold achieves minimum risk_adjusted_value in the list -/
private lemma prudence_fold_achieves_min
    (lambda_val : ℝ) (c : MoralState) (cs : List MoralState) :
    risk_adjusted_value (cs.foldl (prudenceStep lambda_val) c) lambda_val =
      cs.foldl (fun acc m => min acc (risk_adjusted_value m lambda_val)) (risk_adjusted_value c lambda_val) := by
  induction cs generalizing c with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases h : risk_adjusted_value x lambda_val < risk_adjusted_value c lambda_val
    · have hstep : prudenceStep lambda_val c x = x := by unfold prudenceStep; simp [h]
      rw [hstep]
      simp only [min_eq_right (le_of_lt h)]
      exact ih x
    · have hstep : prudenceStep lambda_val c x = c := by unfold prudenceStep; simp [h]
      rw [hstep]
      simp only [min_eq_left (not_lt.mp h)]
      exact ih c

/-- Helper: risk_adjusted_value with lambda=0 equals abs skew -/
private lemma risk_adjusted_value_zero (m : MoralState) :
    risk_adjusted_value m 0 = abs m.skew := by
  unfold risk_adjusted_value
  simp

/-- Helper: prudenceStep at lambda=0 picks the smaller abs skew -/
private lemma prudenceStep_zero_eq_min_skew (a b : MoralState) :
    abs (prudenceStep 0 a b).skew = min (abs a.skew) (abs b.skew) := by
  unfold prudenceStep
  simp only [risk_adjusted_value_zero]
  split_ifs with h
  · exact (min_eq_right (le_of_lt h)).symm
  · exact (min_eq_left (not_lt.mp h)).symm

/-- Helper: foldl prudenceStep at lambda=0 gives min abs skew over list -/
private lemma prudence_fold_zero_min_skew (choices : List MoralState) (start : MoralState) :
    abs (choices.foldl (prudenceStep 0) start).skew =
      choices.foldl (fun acc m => min acc (abs m.skew)) (abs start.skew) := by
  induction choices generalizing start with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    -- The fold is: foldl (prudenceStep 0) (prudenceStep 0 start c) cs
    -- First show what prudenceStep 0 start c gives us
    have h_step : abs (prudenceStep 0 start c).skew = min (abs start.skew) (abs c.skew) :=
      prudenceStep_zero_eq_min_skew start c
    -- Apply IH to the folded result
    rw [ih (prudenceStep 0 start c)]
    -- Now goal is: foldl ... |prudenceStep 0 start c| = foldl ... (min |start| |c|)
    rw [h_step]

/-- Helper: foldl min is associative - we can factor out a min from the start -/
private lemma foldl_min_assoc {α : Type*} [LinearOrder α] (f : MoralState → α)
    (cs : List MoralState) (a b : α) :
    cs.foldl (fun acc m => min acc (f m)) (min a b) =
      min a (cs.foldl (fun acc m => min acc (f m)) b) := by
  induction cs generalizing a b with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.foldl_cons]
    rw [min_assoc a b (f c)]
    rw [ih a (min b (f c))]

/-- Helper: foldl min is at most the initial value -/
private lemma foldl_min_le_init {α : Type*} [LinearOrder α] (f : MoralState → α)
    (xs : List MoralState) (init : α) :
    xs.foldl (fun acc m => min acc (f m)) init ≤ init := by
  induction xs generalizing init with
  | nil => exact le_refl _
  | cons y ys ih =>
    simp only [List.foldl_cons]
    have h1 : min init (f y) ≤ init := min_le_left _ _
    exact le_trans (ih (min init (f y))) h1

/-- Helper: foldl min gives the minimum over the list elements plus initial value -/
private lemma foldl_min_le_of_mem {α : Type*} [LinearOrder α] (f : MoralState → α)
    (xs : List MoralState) (init : α) (x : MoralState) (hx : x ∈ xs) :
    xs.foldl (fun acc m => min acc (f m)) init ≤ f x := by
  induction xs generalizing init with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl heq =>
      rw [heq]
      have h1 : min init (f y) ≤ f y := min_le_right _ _
      exact le_trans (foldl_min_le_init f ys (min init (f y))) h1
    | inr hmem =>
      exact ih (min init (f y)) hmem

/-- Helper: foldl min either equals init or equals some f(x) -/
private lemma foldl_min_eq_init_or_mem {α : Type*} [LinearOrder α] (f : MoralState → α)
    (xs : List MoralState) (init : α) :
    xs.foldl (fun acc m => min acc (f m)) init = init ∨
    ∃ x ∈ xs, xs.foldl (fun acc m => min acc (f m)) init = f x := by
  induction xs generalizing init with
  | nil => left; rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    cases ih (min init (f y)) with
    | inl heq =>
      -- The fold equals min init (f y)
      by_cases h : f y < init
      · right; use y; constructor
        · exact List.mem_cons_self
        · rw [heq]; exact min_eq_right (le_of_lt h)
      · left; rw [heq]; exact min_eq_left (not_lt.mp h)
    | inr hex =>
      obtain ⟨x, hxmem, hxeq⟩ := hex
      right; use x; constructor
      · exact List.mem_cons_of_mem y hxmem
      · exact hxeq

/-- With zero risk penalty, Prudence selects the smaller of
`s` and the wisdom-optimal choice by skew magnitude.

The theorem states that at λ=0, prudent choice equals
min(|s.skew|, |wise.skew|) where wise = WiseChoice s choices.

Mathematical proof sketch:
- PrudentChoice at λ=0 computes argmin_{x ∈ {s} ∪ choices} |x.skew|
- WiseChoice computes argmin_{x ∈ choices} |x.skew|
- So |prudent.skew| = min(|s.skew|, min over choices) = min(|s.skew|, |wise.skew|)

Using properties:
- The fold gives |prudent.skew| ≤ |s.skew| and |prudent.skew| ≤ |c.skew| for all c ∈ choices
- WiseChoice gives |wise.skew| ≤ |c.skew| for all c ∈ choices, and wise ∈ choices
- Therefore |prudent.skew| = min(|s.skew|, |wise.skew|) -/
theorem prudence_zero_lambda_skew_min
  (s : MoralState)
  (choices : List MoralState)
  (h_nonempty : choices ≠ []) :
  let prudent := PrudentChoice s choices 0
  let wise := WiseChoice s choices
  (abs prudent.skew : ℝ) =
    min (abs s.skew : ℝ) (abs wise.skew : ℝ) := by
  simp only
  unfold PrudentChoice
  rw [prudence_fold_zero_min_skew]
  -- Show antisymmetry
  apply le_antisymm
  · -- LHS ≤ RHS: fold gives min over {s} ∪ choices, which is ≤ min(|s|, |wise|)
    apply le_min
    · -- foldl ≤ |s.skew|
      exact foldl_min_le_init (fun m => abs m.skew) choices (abs s.skew)
    · -- foldl ≤ |wise.skew|: wise ∈ choices, and foldl ≤ |c.skew| for all c ∈ choices
      have h_wise_mem : WiseChoice s choices ∈ choices :=
        wiseChoice_mem_of_ne_nil s h_nonempty
      exact foldl_min_le_of_mem (fun m => abs m.skew) choices (abs s.skew)
        (WiseChoice s choices) h_wise_mem
  · -- RHS ≤ LHS: min(|s|, |wise|) ≤ foldl
    -- The foldl is either |s.skew| or |c.skew| for some c ∈ choices
    cases foldl_min_eq_init_or_mem (fun m => abs m.skew) choices (abs s.skew) with
    | inl heq =>
      rw [heq]
      exact min_le_left _ _
    | inr hex =>
      obtain ⟨c, hc_mem, hc_eq⟩ := hex
      rw [hc_eq]
      -- |c.skew| ≥ |wise.skew| since wise minimizes |skew| over choices
      have h_wise_le := wisdom_minimizes_skew_abs s choices h_nonempty c hc_mem
      exact le_trans (min_le_right _ _) h_wise_le

/-- Prudence minimizes the risk-adjusted value across the available choices. -/
theorem prudence_reduces_volatility
  (s : MoralState)
  (choices : List MoralState)
  (lambda_val : ℝ)
  (_h_lambda : 0 < lambda_val) :
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
  have hvar := variance_estimate_nonneg s
  nlinarith

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
  unfold PrudentChoice
  simp only [List.foldl_cons, List.foldl_nil]
  have h_stable_beats_risky : risk_adjusted_value stable lambda_val < risk_adjusted_value risky lambda_val := by
    unfold risk_adjusted_value
    rw [h_skew]
    have h := mul_lt_mul_of_pos_left h_var h_lambda
    linarith
  -- Case split on whether risky beats s
  by_cases h_risky_beats_s : risk_adjusted_value risky lambda_val < risk_adjusted_value s lambda_val
  · -- risky < s, so first step gives risky
    have h_step1 : prudenceStep lambda_val s risky = risky := by
      unfold prudenceStep
      simp only [h_risky_beats_s, ↓reduceIte]
    rw [h_step1]
    -- stable < risky, so second step gives stable
    unfold prudenceStep
    simp only [h_stable_beats_risky, ↓reduceIte]
  · -- risky ≥ s, so first step gives s
    have h_step1 : prudenceStep lambda_val s risky = s := by
      unfold prudenceStep
      simp only [h_risky_beats_s, ↓reduceIte]
    rw [h_step1]
    -- stable < s, so second step gives stable
    unfold prudenceStep
    simp only [h_stable_beats_s, ↓reduceIte]

/-- Prudence tolerates higher skew if variance reduction compensates. -/
theorem prudence_tradeoff
  (s : MoralState)
  (safe risky : MoralState)
  (lambda_val : ℝ)
  (_h_lambda : 0 < lambda_val)
  (_h_skew_order : (abs risky.skew : ℝ) < (abs safe.skew : ℝ))
  (_h_var_order : variance_estimate safe < variance_estimate risky)
  (h_beats_s : risk_adjusted_value safe lambda_val < risk_adjusted_value s lambda_val) :
  lambda_val * (variance_estimate risky - variance_estimate safe) ≥
    ((abs safe.skew : ℝ) - (abs risky.skew : ℝ)) →
  PrudentChoice s [safe, risky] lambda_val = safe := by
  intro h_gap
  unfold PrudentChoice
  simp only [List.foldl_cons, List.foldl_nil]
  -- The gap condition means: safe has lower risk_adjusted_value than risky
  have h_safe_le_risky : risk_adjusted_value safe lambda_val ≤ risk_adjusted_value risky lambda_val := by
    unfold risk_adjusted_value
    linarith
  -- First step: prudenceStep lambda_val s safe
  have h_step1 : prudenceStep lambda_val s safe = safe := by
    unfold prudenceStep
    simp only [h_beats_s, ↓reduceIte]
  rw [h_step1]
  -- Second step: prudenceStep lambda_val safe risky
  unfold prudenceStep
  simp only [not_lt.mpr h_safe_le_risky, ↓reduceIte]

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
    congr 1
    rw [min_assoc, min_assoc, min_comm x y]
  | trans _ _ ih1 ih2 => exact (ih1 init).trans (ih2 init)

/-- Prudence is stable under permutation of choices. -/
theorem prudence_permutation_invariant
  (s : MoralState)
  (choices₁ choices₂ : List MoralState)
  (lambda_val : ℝ)
  (h_perm : choices₁.Perm choices₂) :
  risk_adjusted_value (PrudentChoice s choices₁ lambda_val) lambda_val =
    risk_adjusted_value (PrudentChoice s choices₂ lambda_val) lambda_val := by
  unfold PrudentChoice
  rw [prudence_fold_achieves_min, prudence_fold_achieves_min]
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

end

end Virtues
end Ethics
end IndisputableMonolith
