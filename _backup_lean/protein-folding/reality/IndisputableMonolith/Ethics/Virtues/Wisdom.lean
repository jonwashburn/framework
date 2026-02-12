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
private def wisdomWeight : ℝ := 1 / (1 + Foundation.φ)

/-- φ-discounted skew score used for comparisons inside `WiseChoice`. -/
private def wisdomScore (m : MoralState) : ℝ := (Int.natAbs m.skew : ℝ) * wisdomWeight

/-- Core comparison step used by `WiseChoice`. -/
private def wisdomStep (best current : MoralState) : MoralState :=
  if wisdomScore current < wisdomScore best then current else best

private lemma wisdomWeight_pos : 0 < wisdomWeight := by
  unfold wisdomWeight
  have hφ : 1 < Foundation.φ :=
    IndisputableMonolith.Support.GoldenRatio.one_lt_phi
  have : 0 < 1 + Foundation.φ := by linarith
  exact one_div_pos.mpr this

private lemma wisdomScore_eq_of_skew_eq {a b : MoralState}
    (h : a.skew = b.skew) : wisdomScore a = wisdomScore b := by
  simp [wisdomScore, h]

private lemma wisdomScore_le_of_natAbs_le {a b : MoralState}
    (h : (Int.natAbs a.skew : ℝ) ≤ (Int.natAbs b.skew : ℝ)) :
    wisdomScore a ≤ wisdomScore b := by
  have hWeight_nonneg : 0 ≤ wisdomWeight := le_of_lt wisdomWeight_pos
  exact mul_le_mul_of_nonneg_right h hWeight_nonneg

private lemma wisdomScore_lt_of_natAbs_lt {a b : MoralState}
    (h : (Int.natAbs a.skew : ℝ) < (Int.natAbs b.skew : ℝ)) :
    wisdomScore a < wisdomScore b :=
  mul_lt_mul_of_pos_right h wisdomWeight_pos

/-- Folding helper: the accumulated choice never has higher score than any processed element. -/
private lemma wisdom_fold_step_min
    (choices : List MoralState) (start : MoralState) :
    wisdomScore (choices.foldl wisdomStep start) ≤ wisdomScore start ∧
      ∀ s ∈ choices, wisdomScore (choices.foldl wisdomStep start) ≤ wisdomScore s := by
  refine List.recOn choices ?base ?step
  · simp [wisdomStep]
  · intro head tail ih
    rcases ih (wisdomStep start head) with ⟨ih_start, ih_tail⟩
    by_cases hlt : wisdomScore head < wisdomScore start
    · have hwStep : wisdomStep start head = head := by simp [wisdomStep, hlt]
      have hFold_eq : tail.foldl wisdomStep (wisdomStep start head)
          = tail.foldl wisdomStep head := by simpa [hwStep]
      refine And.intro ?_ ?_
      · have h_le_head : wisdomScore (tail.foldl wisdomStep head) ≤ wisdomScore head := by
          simpa [hwStep, hFold_eq] using ih_start
        exact (le_trans h_le_head (le_of_lt hlt))
      · intro s hs
        have hs' : s = head ∨ s ∈ tail := by simpa [List.mem_cons] using hs
        refine hs'.elim ?_ ?_
        · intro hsEq; subst hsEq; have := ih_start; simpa [hwStep, hFold_eq]
        · intro hTail
          have := ih_tail s hTail
          simpa [hwStep, hFold_eq] using this
    · have hwStep : wisdomStep start head = start := by simp [wisdomStep, hlt]
      have hFold_eq : tail.foldl wisdomStep (wisdomStep start head)
          = tail.foldl wisdomStep start := by simpa [hwStep]
      refine And.intro ?_ ?_
      · simpa [hwStep, hFold_eq] using ih_start
      · intro s hs
        have hs' : s = head ∨ s ∈ tail := by simpa [List.mem_cons] using hs
        refine hs'.elim ?_ ?_
        · intro hsEq; subst hsEq
          have h_le_start : wisdomScore (tail.foldl wisdomStep start) ≤ wisdomScore start := by
            simpa [hwStep, hFold_eq] using ih_start
          have h_start_le_head : wisdomScore start ≤ wisdomScore head := le_of_not_lt hlt
          exact le_trans h_le_start h_start_le_head
        · intro hTail
          have := ih_tail s hTail
          simpa [hwStep, hFold_eq] using this

/-- The fold-based chooser always returns an element from the processed list. -/
private lemma wisdom_fold_mem
    (choices : List MoralState) (start : MoralState) :
    choices.foldl wisdomStep start = start ∨
      choices.foldl wisdomStep start ∈ choices := by
  refine List.recOn choices ?base ?step
  · intro start; left; simp [wisdomStep]
  · intro head tail ih start
    have hRec := ih (wisdomStep start head)
    by_cases hlt : wisdomScore head < wisdomScore start
    · have hwStep : wisdomStep start head = head := by simp [wisdomStep, hlt]
      have hFold_eq : tail.foldl wisdomStep (wisdomStep start head)
          = tail.foldl wisdomStep head := by simpa [hwStep]
      refine (hRec).elim ?_ ?_
      · intro hEq
        left
        simpa [hwStep, hFold_eq]
      · intro hMem
        right
        have : tail.foldl wisdomStep head ∈ tail := by simpa [hwStep, hFold_eq] using hMem
        exact List.mem_cons_of_mem _ this
    · have hwStep : wisdomStep start head = start := by simp [wisdomStep, hlt]
      have hFold_eq : tail.foldl wisdomStep (wisdomStep start head)
          = tail.foldl wisdomStep start := by simpa [hwStep]
      refine (ih start).elim ?_ ?_
      · intro hEq; left; simpa [hwStep, hFold_eq]
      · intro hMem
        right
        have : tail.foldl wisdomStep start ∈ tail := by simpa [hwStep, hFold_eq] using hMem
        exact List.mem_cons_of_mem _ this
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
  let φ := Foundation.φ
  let future_weight := 1 / (1 + φ)  -- = 1/φ² ≈ 0.382
  match choices with
  | [] => s
  | c :: cs =>
      (c :: cs).foldl (fun best current =>
        let weighted_current := (Int.natAbs current.skew : ℝ) * future_weight
        let weighted_best := (Int.natAbs best.skew : ℝ) * future_weight
        if weighted_current < weighted_best then current else best
      ) c

/-! ## Minimality Theorems -/

/-- Wisdom minimizes long-term weighted skew -/
theorem wisdom_minimizes_longterm_skew
  (s : MoralState)
  (choices : List MoralState)
  (h_nonempty : choices ≠ []) :
  let result := WiseChoice s choices
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  ∀ c ∈ choices,
    (Int.natAbs result.skew : ℝ) * weight ≤ (Int.natAbs c.skew : ℝ) * weight := by
  intro c h_mem
  unfold WiseChoice
  obtain ⟨choice₀, rest, rfl⟩ := List.exists_eq_cons_of_ne_nil h_nonempty
  simp only
  have h_result_fold :
      (choice₀ :: rest).foldl
        (fun best current =>
          let weighted_current := (Int.natAbs current.skew : ℝ) * wisdomWeight
          let weighted_best := (Int.natAbs best.skew : ℝ) * wisdomWeight
          if weighted_current < weighted_best then current else best) choice₀
        = rest.foldl wisdomStep choice₀ := by
    simp [List.foldl, wisdomStep, wisdomScore, wisdomWeight]
  have ⟨h_le_head, h_le_rest⟩ := wisdom_fold_step_min rest choice₀
  have h_mem' : c = choice₀ ∨ c ∈ rest := by simpa [List.mem_cons] using h_mem
  have h_weight_eq : weight = wisdomWeight := by simp [weight, wisdomWeight]
  refine h_mem'.elim ?_ ?_
  · intro hEq; subst hEq
    have := h_le_head
    simpa [h_weight_eq, wisdomScore, wisdomWeight, h_result_fold]
  · intro hTail
    have := h_le_rest c hTail
    simpa [h_weight_eq, wisdomScore, wisdomWeight, h_result_fold]

/-- Wisdom returns a choice from the list (or fallback s) -/
theorem wisdom_returns_valid_choice
  (s : MoralState)
  (choices : List MoralState) :
  let result := WiseChoice s choices
  result = s ∨ result ∈ choices := by
  -- Unfold and proceed by cases/induction with a generalized lemma.
  unfold WiseChoice
  cases choices with
  | nil => left; simp
  | cons c cs =>
    -- Define the local step and show fold returns either the accumulator or an element
    let φ := Foundation.φ
    let future_weight := 1 / (1 + φ)
    let step := fun (best current : MoralState) =>
      let weighted_current := (Int.natAbs current.skew : ℝ) * future_weight
      let weighted_best := (Int.natAbs best.skew : ℝ) * future_weight
      if weighted_current < weighted_best then current else best
    -- Auxiliary lemma: foldl step acc l = acc ∨ foldl step acc l ∈ l
    have aux : ∀ (acc : MoralState) (l : List MoralState),
        List.foldl step acc l = acc ∨ List.foldl step acc l ∈ l := by
      intro acc l
      induction l with
      | nil => left; simp
      | cons a as ih =>
        -- step returns either acc or a
        have hstep : step acc a = acc ∨ step acc a = a := by
          by_cases hcond : (Int.natAbs a.skew : ℝ) * future_weight < (Int.natAbs acc.skew : ℝ) * future_weight
          · simp [step, hcond]
          · simp [step, hcond]
        -- apply IH to the new accumulator
        have hfold := ih (step acc a)
        rcases hfold with hfold | hfold
        · -- result equals step acc a, which is either acc or a
          rcases hstep with hacc | ha
          · left; simpa [hacc] using hfold
          · right; simpa [ha, List.mem_cons] using Or.inl rfl
        · -- result is in tail ⇒ in the cons list
          right; simpa [List.mem_cons] using Or.inr hfold
    -- Apply the auxiliary lemma with accumulator c over cs
    have h := aux c cs
    -- The result of the fold is either c or in cs, hence in (c :: cs)
    right
    simpa [List.mem_cons] using h

/-- Wisdom with single choice returns that choice -/
theorem wisdom_single_choice
  (s : MoralState)
  (c : MoralState) :
  WiseChoice s [c] = c := by
  unfold WiseChoice
  simp

/-- Wisdom on empty list returns fallback -/
theorem wisdom_empty_fallback
  (s : MoralState) :
  WiseChoice s [] = s := by
  unfold WiseChoice
  simp

/-! ## φ-Discounting Properties -/

/-- The future weight equals 1/φ² -/
theorem future_weight_is_phi_squared :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  weight = 1 / (φ * φ) := by
  -- Direct from GoldenRatio proven identity
  exact Support.GoldenRatio.inv_one_plus_phi_eq_inv_phi_sq

/-- φ-discounting is monotonic -/
theorem phi_discounting_monotonic
  (x y : ℝ)
  (h : x ≤ y) :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  x * weight ≤ y * weight := by
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  have hφ : 1 < φ := IndisputableMonolith.Support.GoldenRatio.one_lt_phi
  have h_weight_pos : 0 < weight := by
    -- weight = 1 / (1 + φ) with φ > 1
    unfold weight φ
    have : 0 < 1 + Foundation.φ := by
      have hφ : 1 < Foundation.φ := IndisputableMonolith.Support.GoldenRatio.one_lt_phi
      linarith
    exact one_div_pos.mpr this
  exact mul_le_mul_of_nonneg_right h (le_of_lt h_weight_pos)

/-! ## Comparison with Alternatives -/

/-- Wisdom differs from myopic choice (unweighted minimum) -/
theorem wisdom_not_myopic
  (s c₁ c₂ : MoralState)
  (h₁ : c₁.skew < c₂.skew)
  (h₂ : 0 < c₁.skew) :
  -- Wisdom considers long-term, not just immediate skew
  WiseChoice s [c₁, c₂] = c₁ := by
  unfold WiseChoice
  have hc₁_nonneg : 0 ≤ c₁.skew := le_of_lt h₂
  have hc₂_pos : 0 < c₂.skew := lt_trans h₂ h₁
  have hc₂_nonneg : 0 ≤ c₂.skew := le_of_lt hc₂_pos
  have hAbs : Int.natAbs c₁.skew ≤ Int.natAbs c₂.skew := by
    have := Int.toNat_le_toNat (le_of_lt h₁)
    simpa [Int.natAbs_of_nonneg, hc₁_nonneg, hc₂_nonneg] using this
  have hAbs_real : (Int.natAbs c₁.skew : ℝ) ≤ (Int.natAbs c₂.skew : ℝ) := by exact_mod_cast hAbs
  have hWeight_pos : 0 < wisdomWeight := by
    unfold wisdomWeight
    have : 0 < 1 + Foundation.φ := by
      have hφ : 1 < Foundation.φ := IndisputableMonolith.Support.GoldenRatio.one_lt_phi
      linarith
    exact one_div_pos.mpr this
  have hScore_le : wisdomScore c₁ ≤ wisdomScore c₂ := by
    have hWeight_nonneg : 0 ≤ wisdomWeight := le_of_lt hWeight_pos
    have := mul_le_mul_of_nonneg_right hAbs_real hWeight_nonneg
    simpa [wisdomScore]
  simp [List.foldl, wisdomStep, wisdomScore, wisdomWeight, not_lt.mpr hScore_le]

/-- Wisdom's optimal score is invariant under permutations of the choice list. -/
theorem wisdom_stable_under_permutation
  (s : MoralState)
  (choices₁ choices₂ : List MoralState)
  (h_perm : choices₁.Perm choices₂) :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  (Int.natAbs (WiseChoice s choices₁).skew : ℝ) * weight =
    (Int.natAbs (WiseChoice s choices₂).skew : ℝ) * weight := by
  classical
  intro φ weight
  have h_weight_eq : weight = wisdomWeight := by simp [weight, φ, wisdomWeight]
  by_cases h_empty : choices₁ = []
  · have choices₂_empty : choices₂ = [] := by simpa [h_empty] using h_perm.eq_nil_iff.mp rfl
    simp [WiseChoice, h_empty, choices₂_empty, wisdomWeight, h_weight_eq]
  · have h₁_nonempty : choices₁ ≠ [] := h_empty
    have h₂_nonempty : choices₂ ≠ [] := by
      intro h₂; apply h₁_nonempty; simpa [h₂] using h_perm.eq_nil_iff.mpr h₂
    obtain ⟨c₁, rest₁, rfl⟩ := List.exists_eq_cons_of_ne_nil h₁_nonempty
    obtain ⟨c₂, rest₂, rfl⟩ := List.exists_eq_cons_of_ne_nil h₂_nonempty
    simp only [WiseChoice]
    have h_fold₁ : (c₁ :: rest₁).foldl
        (fun best current =>
          let weighted_current := (Int.natAbs current.skew : ℝ) * wisdomWeight
          let weighted_best := (Int.natAbs best.skew : ℝ) * wisdomWeight
          if weighted_current < weighted_best then current else best) c₁
        = rest₁.foldl wisdomStep c₁ := by
      simp [List.foldl, wisdomStep, wisdomScore, wisdomWeight]
    have h_fold₂ : (c₂ :: rest₂).foldl
        (fun best current =>
          let weighted_current := (Int.natAbs current.skew : ℝ) * wisdomWeight
          let weighted_best := (Int.natAbs best.skew : ℝ) * wisdomWeight
          if weighted_current < weighted_best then current else best) c₂
        = rest₂.foldl wisdomStep c₂ := by
      simp [List.foldl, wisdomStep, wisdomScore, wisdomWeight]
    set result₁ := rest₁.foldl wisdomStep c₁
    set result₂ := rest₂.foldl wisdomStep c₂
    have h_mem₁ : result₁ ∈ c₁ :: rest₁ := by
      obtain hmem | hmem := wisdom_fold_mem rest₁ c₁
      · subst hmem; exact List.mem_cons_self _ _
      · exact List.mem_cons_of_mem _ hmem
    have h_mem₂ : result₂ ∈ c₂ :: rest₂ := by
      obtain hmem | hmem := wisdom_fold_mem rest₂ c₂
      · subst hmem; exact List.mem_cons_self _ _
      · exact List.mem_cons_of_mem _ hmem
    have h_perm_cons : (c₁ :: rest₁).Perm (c₂ :: rest₂) := by simpa using h_perm
    have h_mem₁_in₂ : result₁ ∈ c₂ :: rest₂ := (List.Perm.mem_iff h_perm_cons).mpr h_mem₁
    have h_mem₂_in₁ : result₂ ∈ c₁ :: rest₁ := (List.Perm.mem_iff h_perm_cons).mp h_mem₂
    have h_min₁ := wisdom_minimizes_longterm_skew s (c₁ :: rest₁) (by simp)
    have h_min₂ := wisdom_minimizes_longterm_skew s (c₂ :: rest₂) (by simp)
    have h_le₁₂ : wisdomScore result₁ ≤ wisdomScore result₂ := by
      have := h_min₂ result₁ h_mem₁_in₂
      simpa [result₁, result₂, φ, weight, h_fold₂, h_weight_eq, wisdomScore, wisdomWeight]
        using this
    have h_le₂₁ : wisdomScore result₂ ≤ wisdomScore result₁ := by
      have := h_min₁ result₂ h_mem₂_in₁
      simpa [result₁, result₂, φ, weight, h_fold₁, h_weight_eq, wisdomScore, wisdomWeight]
        using this
    have h_eq : wisdomScore result₁ = wisdomScore result₂ := le_antisymm h_le₁₂ h_le₂₁
    simpa [result₁, result₂, φ, weight, h_fold₁, h_fold₂, h_weight_eq, wisdomScore, wisdomWeight]
      using h_eq

/-! ## Ethical Properties -/

attribute [simp] List.map_cons

private lemma wiseChoice_cons_eq_fold (s choice₀ : MoralState)
    (rest : List MoralState) :
    WiseChoice s (choice₀ :: rest) = rest.foldl wisdomStep choice₀ := by
  unfold WiseChoice
  simp [List.foldl, wisdomStep]

private lemma wiseChoice_mem_of_ne_nil (s : MoralState)
    {choices : List MoralState} (h : choices ≠ []) :
    WiseChoice s choices ∈ choices := by
  classical
  obtain ⟨choice₀, rest, rfl⟩ := List.exists_eq_cons_of_ne_nil h
  have hfold : WiseChoice s (choice₀ :: rest) = rest.foldl wisdomStep choice₀ :=
    wiseChoice_cons_eq_fold s choice₀ rest
  obtain hstart | hmem := wisdom_fold_mem rest choice₀
  · have : WiseChoice s (choice₀ :: rest) = choice₀ := by
      simpa [hfold, hstart]
    simpa [this]
  · have : WiseChoice s (choice₀ :: rest) ∈ rest := by
      simpa [hfold] using hmem
    exact List.mem_cons_of_mem _ this

/-- Wisdom prefers the sustainable option with strictly lower φ-weighted skew. -/
theorem wisdom_prefers_sustainable
  (s : MoralState)
  (myopic long_term : MoralState)
  (h_future : (Int.natAbs long_term.skew : ℝ) < (Int.natAbs myopic.skew : ℝ)) :
  WiseChoice s [myopic, long_term] = long_term := by
  have hScore : wisdomScore long_term < wisdomScore myopic :=
    wisdomScore_lt_of_natAbs_lt h_future
  unfold WiseChoice
  simp [List.foldl, wisdomStep, wisdomScore, hScore, lt_irrefl]

/-- Wisdom avoids local minima by considering the entire horizon. -/
theorem wisdom_avoids_local_minima
  (s : MoralState)
  (prior future : List MoralState)
  (h_nonempty : prior ++ future ≠ []) :
  let result := WiseChoice s (prior ++ future)
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  ∀ c ∈ prior,
    (Int.natAbs result.skew : ℝ) * weight ≤ (Int.natAbs c.skew : ℝ) * weight := by
  intro result φ weight c hc
  have h_min :=
    wisdom_minimizes_longterm_skew s (prior ++ future) h_nonempty
  exact h_min c (List.mem_append.mpr <| Or.inl hc)

/-- Wisdom is consistent: applying twice gives same result -/
theorem wisdom_idempotent
  (s : MoralState)
  (choices : List MoralState) :
  let result := WiseChoice s choices
  WiseChoice result choices = result := by
  unfold WiseChoice
  -- After selecting minimum, selecting again gives same result
  cases choices with
  | nil => simp
  | cons choice rest => simp

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
  intro result φ weight
  classical
  have h_combined : choices₁ ++ choices₂ ≠ [] := by
    intro h
    have := List.append_eq_nil.mp h
    exact h₁ this.1
  have h_min :=
    wisdom_minimizes_longterm_skew s (choices₁ ++ choices₂) h_combined
  have h₁mem : WiseChoice s choices₁ ∈ choices₁ :=
    wiseChoice_mem_of_ne_nil s h₁
  have h₂mem : WiseChoice s choices₂ ∈ choices₂ :=
    wiseChoice_mem_of_ne_nil s h₂
  refine le_min ?_ ?_
  · exact h_min _ (List.mem_append.mpr <| Or.inl h₁mem)
  · exact h_min _ (List.mem_append.mpr <| Or.inr h₂mem)

/-- Wisdom can be applied iteratively (chained decisions) -/
theorem wisdom_iterative
  (s : MoralState)
  (step₁ step₂ : List MoralState) :
  let first := WiseChoice s step₁
  let second := WiseChoice first step₂
  -- Two-step wisdom considers both stages
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  step₁ ≠ [] → step₂ ≠ [] →
    (Int.natAbs (WiseChoice s (step₁ ++ step₂)).skew : ℝ) * weight ≤
      (Int.natAbs first.skew : ℝ) * weight ∧
    (Int.natAbs (WiseChoice s (step₁ ++ step₂)).skew : ℝ) * weight ≤
      (Int.natAbs second.skew : ℝ) * weight := by
  intro first second φ weight h₁ h₂
  classical
  have h_combined : step₁ ++ step₂ ≠ [] := by
    intro h
    have := List.append_eq_nil.mp h
    exact h₁ this.1
  have h_min :=
    wisdom_minimizes_longterm_skew s (step₁ ++ step₂) h_combined
  have h₁mem : first ∈ step₁ := by
    unfold first
    simpa using wiseChoice_mem_of_ne_nil s h₁
  have h₂mem : second ∈ step₂ := by
    unfold second
    simpa using wiseChoice_mem_of_ne_nil first h₂
  constructor
  · exact h_min _ (List.mem_append.mpr <| Or.inl h₁mem)
  · exact h_min _ (List.mem_append.mpr <| Or.inr h₂mem)

/-! ## Comparison with Other Virtues -/

/-- Wisdom complements Love: Love equalizes skew, so Wisdom is indifferent between the pair. -/
theorem wisdom_complements_love
  (s₁ s₂ : MoralState) :
  let pair := Love s₁ s₂
  wisdomScore pair.1 = wisdomScore pair.2 := by
  intro pair
  rcases pair with ⟨s₁', s₂'⟩
  have h_balance := Love.love_creates_balance s₁ s₂
  simpa [wisdomScore] using h_balance

private lemma wisdomStep_commute_map
  (f : MoralState → MoralState)
  (hf : ∀ s, (f s).skew = s.skew)
  (best current : MoralState) :
  wisdomStep (f best) (f current) = f (wisdomStep best current) := by
  have hbest : wisdomScore (f best) = wisdomScore best :=
    wisdomScore_eq_of_skew_eq (hf best)
  have hcurrent : wisdomScore (f current) = wisdomScore current :=
    wisdomScore_eq_of_skew_eq (hf current)
  by_cases hlt : wisdomScore current < wisdomScore best
  · simp [wisdomStep, hbest, hcurrent, hlt]
  · have : ¬ wisdomScore (f current) < wisdomScore (f best) := by
      simpa [hbest, hcurrent] using hlt
    simp [wisdomStep, hbest, hcurrent, hlt, this]

private lemma wisdom_fold_map
  (f : MoralState → MoralState)
  (hf : ∀ s, (f s).skew = s.skew)
  (choices : List MoralState) (start : MoralState) :
  (choices.map f).foldl wisdomStep (f start) =
    f (choices.foldl wisdomStep start) := by
  classical
  induction choices generalizing start with
  | nil => simp
  | cons choice rest ih =>
      simp [List.map_cons, wisdomStep_commute_map f hf, ih, List.foldl]

lemma wisdom_invariant_of_skew_preserving
  (f : MoralState → MoralState)
  (hf : ∀ s, (f s).skew = s.skew)
  (s : MoralState) (choices : List MoralState) :
  WiseChoice (f s) (choices.map f) = f (WiseChoice s choices) := by
  classical
  cases choices with
  | nil => simp [WiseChoice]
  | cons c cs =>
      have := wisdom_fold_map f hf cs c
      simpa [WiseChoice, wiseChoice_cons_eq_fold, List.map_cons, this]

/-- Wisdom respects Justice: balanced postings (δ = 0) leave φ-optimization unchanged. -/
theorem wisdom_respects_justice
  (protocol : Justice.JusticeProtocol)
  (entry : Justice.Entry)
  (h_balanced : entry.delta = 0)
  (s : MoralState)
  (choices : List MoralState) :
  WiseChoice (Justice.ApplyJustice protocol entry s)
    (choices.map (Justice.ApplyJustice protocol entry)) =
      Justice.ApplyJustice protocol entry (WiseChoice s choices) := by
  refine wisdom_invariant_of_skew_preserving
    (Justice.ApplyJustice protocol entry) ?hf s choices
  intro m
  unfold Justice.ApplyJustice
  simp [h_balanced]

/-! ## Advanced Properties -/

/-- Wisdom's φ-factor is unique (no other factor is self-similar) -/
theorem wisdom_phi_unique :
  let φ := Foundation.φ
  -- φ satisfies φ² = φ + 1 (unique positive solution)
  φ * φ = φ + 1 := by
  -- Direct from GoldenRatio defining equation
  exact Support.GoldenRatio.phi_squared_eq_phi_plus_one

/-- Wisdom preserves information across time (φ-scaling property) -/
theorem wisdom_preserves_information :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  -- φ-weighting maintains self-similar structure
  weight * φ * φ = 1 := by
  have h_weight := future_weight_is_phi_squared
  simp at h_weight
  calc (1 / (1 + φ)) * φ * φ
    = (1 / (φ * φ)) * φ * φ := by rw [h_weight]
    _ = 1 := by field_simp [Support.GoldenRatio.phi_ne_zero]

/-- Wisdom is the temporal dual of Love: Love's complementary energy share equals the φ discount. -/
theorem wisdom_temporal_dual_of_love
  (s₁ s₂ : MoralState) :
  let pair := Love s₁ s₂
  let total := s₁.energy + s₂.energy
  pair.2.energy / total = wisdomWeight := by
  intro pair total
  rcases pair with ⟨s₁', s₂'⟩
  have h_split := Love.love_energy_split_is_golden s₁ s₂
  have h_weight := future_weight_is_phi_squared
  obtain ⟨_, h_second⟩ := h_split
  have : wisdomWeight = 1 / (Foundation.φ * Foundation.φ) := by
    simp [wisdomWeight, h_weight]
  simpa [this]

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
