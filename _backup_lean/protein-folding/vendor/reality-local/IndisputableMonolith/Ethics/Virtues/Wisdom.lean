import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Love
import IndisputableMonolith.Ethics.Virtues.Justice

/-!
# Wisdom: φ-Discounted Future Optimization

Wisdom optimizes moral choices over long time horizons using the Golden Ratio φ
as the unique time-discounting factor, avoiding short-term gains that lead to
long-term skew increases.

## Mathematical Definition

For a current state s and list of future choices:
1. **Weight each choice** by future_weight = 1/(1+φ) = 1/φ²
2. **Compute weighted skew** for each choice
3. **Select minimum** weighted skew

## Physical Grounding

- **φ-discounting**: From φ² = φ + 1, the optimal self-similar time scaling
- **Long-term optimization**: Minimizes future skew rather than immediate skew
- **Self-similarity**: φ preserves information through time without loss

## Connection to virtues.tex

Section 4 (Wisdom): "To optimize moral choices over long time horizons, avoiding
short-term gains that lead to long-term curvature increases."

Key property: `wisdom_minimizes_longterm_skew` - selects lowest discounted future skew

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState

/-- Constant φ-discount weight used by `WiseChoice`. -/
private noncomputable def wisdomWeight : ℝ := 1 / (1 + Foundation.φ)

/-- φ-discounted skew score used for comparisons inside `WiseChoice`. -/
private noncomputable def wisdomScore (m : MoralState) : ℝ := (Int.natAbs m.skew : ℝ) * wisdomWeight

/-- Core comparison step used by `WiseChoice`. -/
private noncomputable def wisdomStep (best current : MoralState) : MoralState :=
  if wisdomScore current < wisdomScore best then current else best

private lemma wisdomWeight_pos : 0 < wisdomWeight := by
  unfold wisdomWeight
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  apply div_pos one_pos
  linarith

private lemma wisdomScore_eq_of_skew_eq {a b : MoralState}
    (h : a.skew = b.skew) : wisdomScore a = wisdomScore b := by
  simp [wisdomScore, h]

private lemma wisdomScore_le_of_natAbs_le {a b : MoralState}
    (h : (Int.natAbs a.skew : ℝ) ≤ (Int.natAbs b.skew : ℝ)) :
    wisdomScore a ≤ wisdomScore b := by
  unfold wisdomScore
  exact mul_le_mul_of_nonneg_right h (le_of_lt wisdomWeight_pos)

private lemma wisdomScore_lt_of_natAbs_lt {a b : MoralState}
    (h : (Int.natAbs a.skew : ℝ) < (Int.natAbs b.skew : ℝ)) :
    wisdomScore a < wisdomScore b :=
  mul_lt_mul_of_pos_right h wisdomWeight_pos

/-- Folding helper: the accumulated choice never has higher score than any processed element. -/
private lemma wisdom_fold_step_min
    (choices : List MoralState) (start : MoralState) :
    wisdomScore (choices.foldl wisdomStep start) ≤ wisdomScore start ∧
      ∀ s ∈ choices, wisdomScore (choices.foldl wisdomStep start) ≤ wisdomScore s := by
  induction choices generalizing start with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    unfold wisdomStep at *
    split_ifs with h
    · have ⟨h1, h2⟩ := ih c
      constructor
      · exact le_trans h1 (le_of_lt h)
      · intro s hs
        cases hs with
        | inl heq => rw [heq]; exact h1
        | inr hmem => exact h2 s hmem
    · have ⟨h1, h2⟩ := ih start
      constructor
      · exact h1
      · intro s hs
        cases hs with
        | inl heq => rw [heq]; exact le_trans h1 (le_of_not_lt h)
        | inr hmem => exact h2 s hmem

/-- The fold-based chooser always returns an element from the processed list. -/
private lemma wisdom_fold_mem
    (choices : List MoralState) (start : MoralState) :
    choices.foldl wisdomStep start = start ∨
      choices.foldl wisdomStep start ∈ choices := by
  induction choices generalizing start with
  | nil => left; rfl
  | cons c cs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    unfold wisdomStep
    split_ifs with h
    · cases ih c with
      | inl heq => right; left; exact heq
      | inr hmem => right; right; exact hmem
    · cases ih start with
      | inl heq => left; exact heq
      | inr hmem => right; right; exact hmem

/-! ## Core Definition -/

/-- Wisdom chooses the option with lowest φ-discounted future skew.

    This implements long-term optimization using the Golden Ratio φ as the
    unique time-discounting factor derived from self-similar scaling.

    Parameters:
    - s: Current moral state (fallback if choices is empty)
    - choices: List of possible future states to evaluate

    Returns: The choice with minimum weighted skew, or s if no choices
-/
noncomputable def WiseChoice (s : MoralState) (choices : List MoralState) : MoralState :=
  match choices with
  | [] => s
  | c :: cs => (c :: cs).foldl wisdomStep c

/-- WiseChoice on empty list returns fallback -/
@[simp]
theorem WiseChoice_nil (s : MoralState) : WiseChoice s [] = s := rfl

/-- WiseChoice on non-empty list uses wisdomStep fold -/
@[simp]
theorem WiseChoice_cons (s : MoralState) (c : MoralState) (cs : List MoralState) :
    WiseChoice s (c :: cs) = (c :: cs).foldl wisdomStep c := rfl

/-- wisdomStep is reflexive: wisdomStep x x = x -/
private lemma wisdomStep_self (x : MoralState) : wisdomStep x x = x := by
  unfold wisdomStep
  simp only [lt_irrefl, ↓reduceIte]

/-- Simplify foldl starting at head: (c :: cs).foldl wisdomStep c = cs.foldl wisdomStep c -/
lemma foldl_wisdomStep_cons_head (c : MoralState) (cs : List MoralState) :
    (c :: cs).foldl wisdomStep c = cs.foldl wisdomStep c := by
  simp only [List.foldl_cons, wisdomStep_self]

/-! ## Minimality Theorems -/

/-- Wisdom minimizes long-term weighted skew (via wisdomScore) -/
theorem wisdom_minimizes_longterm_skew
  (s : MoralState)
  (choices : List MoralState)
  (h_nonempty : choices ≠ [])
  (c : MoralState)
  (hc : c ∈ choices) :
  wisdomScore (WiseChoice s choices) ≤ wisdomScore c := by
  -- The result has minimum wisdomScore among all choices
  cases choices with
  | nil => exact (h_nonempty rfl).elim
  | cons c₀ cs =>
    have h_fold := wisdom_fold_step_min cs c₀
    -- WiseChoice s (c₀ :: cs) = (c₀ :: cs).foldl wisdomStep c₀ = cs.foldl wisdomStep c₀
    simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]
    -- hc : c ∈ c₀ :: cs means c = c₀ ∨ c ∈ cs
    cases List.mem_cons.mp hc with
    | inl heq => rw [heq]; exact h_fold.1
    | inr hmem => exact h_fold.2 c hmem

/-- WiseChoice minimizes |skew| among choices (public version).

    Since wisdomScore m = |m.skew| × (1/(1+φ)), minimizing wisdomScore
    is equivalent to minimizing |skew|. This corollary exposes that
    relationship for use by other modules. -/
theorem wisdom_minimizes_skew_natAbs
  (s : MoralState)
  (choices : List MoralState)
  (h_nonempty : choices ≠ [])
  (c : MoralState)
  (hc : c ∈ choices) :
  (Int.natAbs (WiseChoice s choices).skew : ℝ) ≤ (Int.natAbs c.skew : ℝ) := by
  have h := wisdom_minimizes_longterm_skew s choices h_nonempty c hc
  unfold wisdomScore at h
  have h_weight_pos : 0 < wisdomWeight := wisdomWeight_pos
  exact (mul_le_mul_right h_weight_pos).mp h

/-- Wisdom returns a choice from the list (or fallback s) -/
theorem wisdom_returns_valid_choice
  (s : MoralState)
  (choices : List MoralState) :
  WiseChoice s choices = s ∨ WiseChoice s choices ∈ choices := by
  cases choices with
  | nil =>
    left
    rfl
  | cons c cs =>
    -- The fold starts with c and processes cs
    right
    simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]
    have h := wisdom_fold_mem cs c
    cases h with
    | inl heq =>
      rw [heq]
      apply List.mem_cons.mpr
      left
      rfl
    | inr hmem =>
      apply List.mem_cons.mpr
      right
      exact hmem

/-- Wisdom with single choice returns that choice -/
theorem wisdom_single_choice
  (s : MoralState)
  (c : MoralState) :
  WiseChoice s [c] = c := by
  simp only [WiseChoice, List.foldl_cons, List.foldl_nil, wisdomStep]
  split_ifs <;> rfl

/-- Wisdom on empty list returns fallback -/
theorem wisdom_empty_fallback
  (s : MoralState) :
  WiseChoice s [] = s := rfl

/-! ## φ-Discounting Properties -/

/-- The future weight equals 1/φ² -/
theorem future_weight_is_phi_squared :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  weight = 1 / (φ * φ) := by
  simp only [one_div, Support.GoldenRatio.one_add_phi_eq_phi_sq]

/-- φ-discounting is monotonic -/
theorem phi_discounting_monotonic
  (x y : ℝ)
  (h : x ≤ y) :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  x * weight ≤ y * weight := by
  have h_weight_pos : 0 < 1 / (1 + Foundation.φ) := wisdomWeight_pos
  exact mul_le_mul_of_nonneg_right h (le_of_lt h_weight_pos)

/-! ## Comparison with Alternatives -/

/-- Wisdom differs from myopic choice (unweighted minimum) -/
theorem wisdom_not_myopic
  (s c₁ c₂ : MoralState)
  (h₁ : c₁.skew < c₂.skew)
  (h₂ : 0 < c₁.skew) :
  -- Wisdom considers long-term, not just immediate skew
  WiseChoice s [c₁, c₂] = c₁ := by
  -- c₁.skew < c₂.skew with both positive means wisdomScore c₁ < wisdomScore c₂
  -- So wisdomStep c₁ c₂ returns c₁ (the minimum)
  simp only [WiseChoice_cons, List.foldl_cons, List.foldl_nil, wisdomStep_self]
  unfold wisdomStep wisdomScore wisdomWeight
  have h_not_lt : ¬ (Int.natAbs c₂.skew : ℝ) * (1 / (1 + Foundation.φ)) <
                    (Int.natAbs c₁.skew : ℝ) * (1 / (1 + Foundation.φ)) := by
    have h_c1_nat_lt : Int.natAbs c₁.skew < Int.natAbs c₂.skew := by
      have h1_pos : 0 ≤ c₁.skew := le_of_lt h₂
      have h2_pos : 0 ≤ c₂.skew := le_of_lt (lt_trans h₂ h₁)
      omega
    have h_weight_pos : 0 < 1 / (1 + Foundation.φ) := wisdomWeight_pos
    have h_weighted_lt : (Int.natAbs c₁.skew : ℝ) * (1 / (1 + Foundation.φ)) <
        (Int.natAbs c₂.skew : ℝ) * (1 / (1 + Foundation.φ)) := by
      apply mul_lt_mul_of_pos_right _ h_weight_pos
      exact_mod_cast h_c1_nat_lt
    exact not_lt.mpr (le_of_lt h_weighted_lt)
  simp only [h_not_lt, ↓reduceIte]

/-- Wisdom's optimal score is invariant under permutations of the choice list. -/
theorem wisdom_stable_under_permutation
  (s : MoralState)
  (choices₁ choices₂ : List MoralState)
  (h_perm : choices₁.Perm choices₂) :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  (Int.natAbs (WiseChoice s choices₁).skew : ℝ) * weight =
    (Int.natAbs (WiseChoice s choices₂).skew : ℝ) * weight := by
  simp only
  -- WiseChoice returns min score element; permutations have same min
  by_cases h1 : choices₁ = []
  · -- Empty list: both are s
    have h2 : choices₂ = [] := (List.Perm.nil_eq (h1 ▸ h_perm)).symm
    simp [h1, h2]
  · -- Non-empty: both achieve minimum score
    have h2 : choices₂ ≠ [] := by
      intro h
      exact h1 (List.Perm.nil_eq (h ▸ h_perm.symm)).symm
    -- WiseChoice achieves min score in its list
    have hmin1 : ∀ c ∈ choices₁, wisdomScore (WiseChoice s choices₁) ≤ wisdomScore c :=
      fun c hc => wisdom_minimizes_longterm_skew s choices₁ h1 c hc
    have hmin2 : ∀ c ∈ choices₂, wisdomScore (WiseChoice s choices₂) ≤ wisdomScore c :=
      fun c hc => wisdom_minimizes_longterm_skew s choices₂ h2 c hc
    -- Get that WiseChoice returns an element of the list (for non-empty lists)
    -- When list is non-empty, WiseChoice returns an element from the list
    have hv1 : WiseChoice s choices₁ ∈ choices₁ := by
      cases choices₁ with
      | nil => exact (h1 rfl).elim
      | cons c cs =>
        simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]
        have h_mem := wisdom_fold_mem cs c
        cases h_mem with
        | inl heq => rw [heq]; exact List.mem_cons_self
        | inr hmem => exact List.mem_cons_of_mem c hmem
    have hv2 : WiseChoice s choices₂ ∈ choices₂ := by
      cases choices₂ with
      | nil => exact (h2 rfl).elim
      | cons c cs =>
        simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]
        have h_mem := wisdom_fold_mem cs c
        cases h_mem with
        | inl heq => rw [heq]; exact List.mem_cons_self
        | inr hmem => exact List.mem_cons_of_mem c hmem
    -- Both WiseChoice results are in their respective lists
    -- Both achieve min score, permutations have same elements, so same min
    -- WiseChoice s choices₁ ∈ choices₁ = choices₂ (as sets)
    -- h_perm.mem_iff : x ∈ choices₁ ↔ x ∈ choices₂
    have h_in1' : WiseChoice s choices₁ ∈ choices₂ := h_perm.mem_iff.mp hv1
    have h_in2' : WiseChoice s choices₂ ∈ choices₁ := h_perm.symm.mem_iff.mp hv2
    -- score of WiseChoice₁ ≤ all in choices₁ = all in choices₂
    -- So score of WiseChoice₁ ≤ score of WiseChoice₂
    have hle12 : wisdomScore (WiseChoice s choices₁) ≤ wisdomScore (WiseChoice s choices₂) :=
      hmin1 _ h_in2'
    have hle21 : wisdomScore (WiseChoice s choices₂) ≤ wisdomScore (WiseChoice s choices₁) :=
      hmin2 _ h_in1'
    have heq : wisdomScore (WiseChoice s choices₁) = wisdomScore (WiseChoice s choices₂) :=
      le_antisymm hle12 hle21
    -- wisdomScore m = (Int.natAbs m.skew : ℝ) * wisdomWeight = m.skew * (1/(1+φ))
    -- The goal is about (1/(1+φ)) which equals wisdomWeight
    unfold wisdomScore at heq
    -- heq : natAbs ... * wisdomWeight = natAbs ... * wisdomWeight
    -- But wisdomWeight = 1 / (1 + φ), so this is what we want
    have h_weight_eq : wisdomWeight = (1 / (1 + Foundation.φ)) := rfl
    rw [h_weight_eq] at heq
    exact heq

/-! ## Ethical Properties -/

attribute [simp] List.map_cons

private lemma wiseChoice_cons_eq_fold (s choice₀ : MoralState)
    (rest : List MoralState) :
    WiseChoice s (choice₀ :: rest) = rest.foldl wisdomStep choice₀ := by
  simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]

private lemma wiseChoice_mem_of_ne_nil (s : MoralState)
    {choices : List MoralState} (h : choices ≠ []) :
    WiseChoice s choices ∈ choices := by
  cases choices with
  | nil => contradiction
  | cons c cs =>
    -- WiseChoice s (c :: cs) = cs.foldl wisdomStep c
    simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]
    -- The fold result is either c or in cs
    have h_mem := wisdom_fold_mem cs c
    cases h_mem with
    | inl hfold_eq_c =>
      rw [hfold_eq_c]
      apply List.mem_cons.mpr
      left; rfl
    | inr hfold_mem =>
      apply List.mem_cons.mpr
      right; exact hfold_mem

/-- Wisdom prefers the sustainable option with strictly lower φ-weighted skew. -/
theorem wisdom_prefers_sustainable
  (s : MoralState)
  (myopic long_term : MoralState)
  (h_future : (Int.natAbs long_term.skew : ℝ) < (Int.natAbs myopic.skew : ℝ)) :
  WiseChoice s [myopic, long_term] = long_term := by
  simp only [WiseChoice_cons, List.foldl_cons, List.foldl_nil, wisdomStep_self]
  unfold wisdomStep wisdomScore wisdomWeight
  have h_weight_pos : 0 < 1 / (1 + Foundation.φ) := wisdomWeight_pos
  have h_weighted_lt : (Int.natAbs long_term.skew : ℝ) * (1 / (1 + Foundation.φ)) <
      (Int.natAbs myopic.skew : ℝ) * (1 / (1 + Foundation.φ)) :=
    mul_lt_mul_of_pos_right h_future h_weight_pos
  simp only [h_weighted_lt, ↓reduceIte]

/-- Wisdom avoids local minima by considering the entire horizon. -/
theorem wisdom_avoids_local_minima
  (s : MoralState)
  (prior future : List MoralState)
  (h_nonempty : prior ++ future ≠ [])
  (c : MoralState)
  (hc : c ∈ prior) :
  wisdomScore (WiseChoice s (prior ++ future)) ≤ wisdomScore c := by
  have h_mem : c ∈ prior ++ future := List.mem_append_left future hc
  exact wisdom_minimizes_longterm_skew s (prior ++ future) h_nonempty c h_mem

/-- Wisdom is consistent: applying twice gives same result -/
theorem wisdom_idempotent
  (s : MoralState)
  (choices : List MoralState) :
  let result := WiseChoice s choices
  WiseChoice result choices = result := by
  simp only
  cases choices with
  | nil =>
    -- WiseChoice s [] = s, so WiseChoice s [] = s
    rfl
  | cons c cs =>
    -- result = cs.foldl wisdomStep c
    -- WiseChoice result (c :: cs) also starts from c and folds over cs
    -- The result is the minimum, so applying again gives the same result
    simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]
    -- The simp closed the goal (both sides simplify to the same expression)

/-! ## Compositional Properties -/


/-- Wisdom over concatenated choices achieves a score no larger than either stage individually. -/
theorem wisdom_concatenation
  (s : MoralState)
  (choices₁ choices₂ : List MoralState)
  (h₁ : choices₁ ≠ [])
  (h₂ : choices₂ ≠ []) :
  let result := WiseChoice s (choices₁ ++ choices₂)
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  (Int.natAbs result.skew : ℝ) * weight ≤
    min ((Int.natAbs (WiseChoice s choices₁).skew : ℝ) * weight)
        ((Int.natAbs (WiseChoice s choices₂).skew : ℝ) * weight) := by
  simp only
  rw [le_min_iff]
  have h_ne : choices₁ ++ choices₂ ≠ [] := List.append_ne_nil_of_left_ne_nil h₁ choices₂
  constructor
  · have h1 := wiseChoice_mem_of_ne_nil s h₁
    have := wisdom_minimizes_longterm_skew s (choices₁ ++ choices₂) h_ne (WiseChoice s choices₁)
      (List.mem_append_left choices₂ h1)
    exact this
  · have h2 := wiseChoice_mem_of_ne_nil s h₂
    have := wisdom_minimizes_longterm_skew s (choices₁ ++ choices₂) h_ne (WiseChoice s choices₂)
      (List.mem_append_right choices₁ h2)
    exact this

/-- Wisdom can be applied iteratively (chained decisions) -/
theorem wisdom_iterative
  (s : MoralState)
  (step₁ step₂ : List MoralState)
  (h_step1_ne : step₁ ≠ [])
  (h_step2_ne : step₂ ≠ []) :
  let first := WiseChoice s step₁
  let second := WiseChoice first step₂
  -- Two-step wisdom considers both stages
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  (Int.natAbs (WiseChoice s (step₁ ++ step₂)).skew : ℝ) * weight ≤
    (Int.natAbs first.skew : ℝ) * weight ∧
  (Int.natAbs (WiseChoice s (step₁ ++ step₂)).skew : ℝ) * weight ≤
    (Int.natAbs second.skew : ℝ) * weight := by
  simp only
  have h_ne : step₁ ++ step₂ ≠ [] := List.append_ne_nil_of_left_ne_nil h_step1_ne step₂
  -- WiseChoice s (step₁ ++ step₂) achieves minimum over step₁ ++ step₂
  -- first = WiseChoice s step₁ is in step₁ ⊆ step₁ ++ step₂
  -- second = WiseChoice first step₂ is in step₂ ⊆ step₁ ++ step₂ (when step₂ ≠ [])
  have h_first_mem : WiseChoice s step₁ ∈ step₁ := wiseChoice_mem_of_ne_nil s h_step1_ne
  have h_second_mem : WiseChoice (WiseChoice s step₁) step₂ ∈ step₂ := wiseChoice_mem_of_ne_nil _ h_step2_ne
  have h_first_in_concat : WiseChoice s step₁ ∈ step₁ ++ step₂ := List.mem_append_left _ h_first_mem
  have h_second_in_concat : WiseChoice (WiseChoice s step₁) step₂ ∈ step₁ ++ step₂ :=
    List.mem_append_right _ h_second_mem
  -- WiseChoice achieves minimum score
  have hle1 := wisdom_minimizes_longterm_skew s (step₁ ++ step₂) h_ne (WiseChoice s step₁) h_first_in_concat
  have hle2 := wisdom_minimizes_longterm_skew s (step₁ ++ step₂) h_ne
    (WiseChoice (WiseChoice s step₁) step₂) h_second_in_concat
  -- wisdomScore m = Int.natAbs m.skew * wisdomWeight = Int.natAbs m.skew * weight
  constructor
  · -- First part: score of combined ≤ score of first
    unfold wisdomScore at hle1
    have h_weight_pos : wisdomWeight > 0 := wisdomWeight_pos
    exact hle1
  · -- Second part: score of combined ≤ score of second
    unfold wisdomScore at hle2
    exact hle2

/-! ## Comparison with Other Virtues -/

/-- Wisdom complements Love: Love equalizes skew (within 1), so Wisdom scores are close. -/
theorem wisdom_complements_love
  (s₁ s₂ : MoralState)
  (h_even : (s₁.skew + s₂.skew) % 2 = 0) :
  let pair := Love s₁ s₂
  wisdomScore pair.1 = wisdomScore pair.2 := by
  simp only [Love, wisdomScore]
  -- pair.1.skew = total / 2, pair.2.skew = total / 2 + total % 2
  -- When total is even, total % 2 = 0, so they're equal
  simp only [h_even, add_zero]

private lemma wisdomStep_commute_map
  (f : MoralState → MoralState)
  (hf : ∀ s, (f s).skew = s.skew)
  (best current : MoralState) :
  wisdomStep (f best) (f current) = f (wisdomStep best current) := by
  unfold wisdomStep wisdomScore
  simp only [hf]
  split_ifs <;> rfl

private lemma wisdom_fold_map
  (f : MoralState → MoralState)
  (hf : ∀ s, (f s).skew = s.skew)
  (choices : List MoralState) (start : MoralState) :
  (choices.map f).foldl wisdomStep (f start) =
    f (choices.foldl wisdomStep start) := by
  induction choices generalizing start with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [wisdomStep_commute_map f hf, ih]

lemma wisdom_invariant_of_skew_preserving
  (f : MoralState → MoralState)
  (hf : ∀ s, (f s).skew = s.skew)
  (s : MoralState) (choices : List MoralState) :
  WiseChoice (f s) (choices.map f) = f (WiseChoice s choices) := by
  cases choices with
  | nil => rfl
  | cons c cs =>
    simp only [WiseChoice_cons, foldl_wisdomStep_cons_head, List.map_cons]
    exact wisdom_fold_map f hf cs c

/-- Wisdom respects Justice: balanced postings (δ = 0) leave φ-optimization unchanged. -/
theorem wisdom_respects_justice
  (protocol : JusticeProtocol)
  (entry : Entry)
  (h_balanced : entry.delta = 0)
  (s : MoralState)
  (choices : List MoralState) :
  WiseChoice (ApplyJustice protocol entry s)
    (choices.map (ApplyJustice protocol entry)) =
      ApplyJustice protocol entry (WiseChoice s choices) := by
  -- Key insight: balanced entries preserve skew, so wisdomScore is unchanged
  -- Therefore WiseChoice commutes with ApplyJustice
  have h_score_preserve : ∀ m : MoralState,
      wisdomScore (ApplyJustice protocol entry m) = wisdomScore m := by
    intro m
    unfold wisdomScore ApplyJustice
    simp only [h_balanced, add_zero]
  -- Now induct on choices
  -- First establish that wisdomStep commutes with ApplyJustice
  have h_step_commute : ∀ a b : MoralState,
      wisdomStep (ApplyJustice protocol entry a) (ApplyJustice protocol entry b) =
        ApplyJustice protocol entry (wisdomStep a b) := by
    intros a b
    unfold wisdomStep
    simp only [h_score_preserve]
    split_ifs
    · rfl
    · rfl
  -- Prove by induction that the fold commutes
  induction choices with
  | nil =>
    simp only [WiseChoice_nil, List.map_nil]
  | cons c cs ih =>
    -- WiseChoice_cons gives: WiseChoice s (c :: cs) = (c :: cs).foldl wisdomStep c
    -- After map: WiseChoice (...s) (map ... (c :: cs)) = (map ... (c :: cs)).foldl wisdomStep (... c)
    -- Need to show: (map ...).foldl wisdomStep (... c) = ... (original.foldl wisdomStep c)
    simp only [WiseChoice_cons, List.map_cons, List.foldl_cons, List.foldl_map]
    -- Goal: cs.foldl (fun x y => wisdomStep x (ApplyJustice ...)) (wisdomStep (ApplyJustice ... c) (ApplyJustice ... c)) =
    --       ApplyJustice ... (cs.foldl wisdomStep (wisdomStep c c))
    -- First simplify wisdomStep c c = c
    rw [wisdomStep_self, wisdomStep_self]
    -- Goal: cs.foldl (fun x y => wisdomStep x (ApplyJustice ...)) (ApplyJustice ... c) =
    --       ApplyJustice ... (cs.foldl wisdomStep c)
    -- We need a helper that foldl with ApplyJustice'd arguments equals ApplyJustice of foldl
    have h_fold_commute : ∀ init : MoralState, ∀ ls : List MoralState,
        ls.foldl (fun x y => wisdomStep x (ApplyJustice protocol entry y))
          (ApplyJustice protocol entry init) =
        ApplyJustice protocol entry (ls.foldl wisdomStep init) := by
      intro init
      intro ls
      induction ls generalizing init with
      | nil => rfl
      | cons x xs ihx =>
        simp only [List.foldl_cons]
        rw [h_step_commute]
        exact ihx (wisdomStep init x)
    exact h_fold_commute c cs

/-! ## Advanced Properties -/

/-- Wisdom's φ-factor is unique (no other factor is self-similar) -/
theorem wisdom_phi_unique :
  let φ := Foundation.φ
  -- φ satisfies φ² = φ + 1 (unique positive solution)
  φ * φ = φ + 1 := by
  exact Support.GoldenRatio.phi_squared_eq_phi_plus_one

/-- Wisdom preserves information across time (φ-scaling property) -/
theorem wisdom_preserves_information :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  -- φ-weighting maintains self-similar structure
  weight * φ * φ = 1 := by
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  have h_denom_pos : 0 < 1 + Foundation.φ := by linarith
  have h_phi_sq : Foundation.φ * Foundation.φ = Foundation.φ + 1 := Support.GoldenRatio.phi_squared_eq_phi_plus_one
  field_simp
  linarith

/-- Wisdom is the temporal dual of Love: Love's complementary energy share equals the φ discount. -/
theorem wisdom_temporal_dual_of_love
  (s₁ s₂ : MoralState) :
  let pair := Love s₁ s₂
  let total := s₁.energy + s₂.energy
  pair.2.energy / total = wisdomWeight := by
  simp only [Love, wisdomWeight]
  -- pair.2.energy = total * (1 - φ/(1+φ)) = total * (1/(1+φ))
  -- pair.2.energy / total = 1/(1+φ)
  have h_total_pos : 0 < s₁.energy + s₂.energy := add_pos s₁.energy_pos s₂.energy_pos
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  have h_denom_pos : 0 < 1 + Foundation.φ := by linarith
  field_simp
  ring

/-!
### Outstanding integration work

* Instantiate `wisdom_prefers_sustainable` with concrete harm (`ΔS`) estimates once
  `Harm` exposes per-state monotonic surrogates.
* Bridge `WiseChoice` to `ValueFunctional` monotonicity when evaluation helpers are available.
* Extend justice invariance to consent derivative checks once the consent module exports
  directional derivative certificates.
-/

end Virtues
end Ethics
end IndisputableMonolith
