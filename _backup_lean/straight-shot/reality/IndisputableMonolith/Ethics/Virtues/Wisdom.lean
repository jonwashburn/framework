import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.Ethics.Virtues.Love
import IndisputableMonolith.Ethics.Virtues.Justice

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState

/-- Constant φ-discount weight used by `WiseChoice`. -/
private noncomputable def wisdomWeight : ℝ := 1 / (1 + Foundation.φ)

/-- φ-discounted skew score used for comparisons inside `WiseChoice`. -/
private noncomputable def wisdomScore (m : MoralState) : ℝ := (abs m.skew) * wisdomWeight

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

private lemma wisdomScore_le_of_abs_le {a b : MoralState}
    (h : (abs a.skew) ≤ (abs b.skew)) :
    wisdomScore a ≤ wisdomScore b := by
  unfold wisdomScore
  exact mul_le_mul_of_nonneg_right h (le_of_lt wisdomWeight_pos)

private lemma wisdomScore_lt_of_abs_lt {a b : MoralState}
    (h : (abs a.skew) < (abs b.skew)) :
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
        | inl heq => rw [heq]; exact le_trans h1 (le_of_not_gt h)
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

noncomputable def WiseChoice (s : MoralState) (choices : List MoralState) : MoralState :=
  match choices with
  | [] => s
  | c :: cs => (c :: cs).foldl wisdomStep c

@[simp]
theorem WiseChoice_nil (s : MoralState) : WiseChoice s [] = s := rfl

@[simp]
theorem WiseChoice_cons (s : MoralState) (c : MoralState) (cs : List MoralState) :
    WiseChoice s (c :: cs) = (c :: cs).foldl wisdomStep c := rfl

private lemma wisdomStep_self (x : MoralState) : wisdomStep x x = x := by
  unfold wisdomStep
  simp only [lt_irrefl, ↓reduceIte]

lemma foldl_wisdomStep_cons_head (c : MoralState) (cs : List MoralState) :
    (c :: cs).foldl wisdomStep c = cs.foldl wisdomStep c := by
  simp only [List.foldl_cons, wisdomStep_self]

/-- Wisdom minimizes long-term weighted skew (via wisdomScore) -/
theorem wisdom_minimizes_longterm_skew
  (s : MoralState)
  (choices : List MoralState)
  (h_nonempty : choices ≠ [])
  (c : MoralState)
  (hc : c ∈ choices) :
  wisdomScore (WiseChoice s choices) ≤ wisdomScore c := by
  cases choices with
  | nil => exact (h_nonempty rfl).elim
  | cons c₀ cs =>
    have h_fold := wisdom_fold_step_min cs c₀
    simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]
    cases List.mem_cons.mp hc with
    | inl heq => rw [heq]; exact h_fold.1
    | inr hmem => exact h_fold.2 c hmem

/-- WiseChoice minimizes |skew| among choices (public version). -/
theorem wisdom_minimizes_skew_abs
  (s : MoralState)
  (choices : List MoralState)
  (h_nonempty : choices ≠ [])
  (c : MoralState)
  (hc : c ∈ choices) :
  abs (WiseChoice s choices).skew ≤ abs c.skew := by
  have h := wisdom_minimizes_longterm_skew s choices h_nonempty c hc
  unfold wisdomScore at h
  have h_weight_pos : 0 < wisdomWeight := wisdomWeight_pos
  exact le_of_mul_le_mul_right h h_weight_pos

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

/-- Wisdom differs from myopic choice (unweighted minimum) -/
theorem wisdom_not_myopic
  (s c₁ c₂ : MoralState)
  (h₁ : c₁.skew < c₂.skew)
  (h₂ : 0 < c₁.skew) :
  WiseChoice s [c₁, c₂] = c₁ := by
  simp only [WiseChoice_cons, List.foldl_cons, List.foldl_nil, wisdomStep_self]
  unfold wisdomStep wisdomScore wisdomWeight
  have h_not_lt : ¬ (abs c₂.skew) * (1 / (1 + Foundation.φ)) <
                    (abs c₁.skew) * (1 / (1 + Foundation.φ)) := by
    have h_abs_lt : abs c₁.skew < abs c₂.skew := by
      have h1_pos : 0 ≤ c₁.skew := le_of_lt h₂
      have h2_pos : 0 ≤ c₂.skew := le_of_lt (lt_trans h₂ h₁)
      simp [abs_of_nonneg h1_pos, abs_of_nonneg h2_pos, h₁]
    have h_weight_pos : 0 < 1 / (1 + Foundation.φ) := wisdomWeight_pos
    have h_weighted_lt : (abs c₁.skew) * (1 / (1 + Foundation.φ)) <
        (abs c₂.skew) * (1 / (1 + Foundation.φ)) := by
      apply mul_lt_mul_of_pos_right h_abs_lt h_weight_pos
    exact not_lt.mpr (le_of_lt h_weighted_lt)
  simp only [h_not_lt, ↓reduceIte]

/-- Wisdom's optimal score is invariant under permutations of the choice list. -/
theorem wisdom_stable_under_permutation
  (s : MoralState)
  (choices₁ choices₂ : List MoralState)
  (h_perm : choices₁.Perm choices₂) :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  (abs (WiseChoice s choices₁).skew) * weight =
    (abs (WiseChoice s choices₂).skew) * weight := by
  simp only
  by_cases h1 : choices₁ = []
  · have h2 : choices₂ = [] := (List.Perm.nil_eq (h1 ▸ h_perm)).symm
    simp [h1, h2]
  · have h2 : choices₂ ≠ [] := by
      intro h
      exact h1 (List.Perm.nil_eq (h ▸ h_perm.symm)).symm
    have hmin1 : ∀ c ∈ choices₁, wisdomScore (WiseChoice s choices₁) ≤ wisdomScore c :=
      fun c hc => wisdom_minimizes_longterm_skew s choices₁ h1 c hc
    have hmin2 : ∀ c ∈ choices₂, wisdomScore (WiseChoice s choices₂) ≤ wisdomScore c :=
      fun c hc => wisdom_minimizes_longterm_skew s choices₂ h2 c hc
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
    have h_in1' : WiseChoice s choices₁ ∈ choices₂ := h_perm.mem_iff.mp hv1
    have h_in2' : WiseChoice s choices₂ ∈ choices₁ := h_perm.symm.mem_iff.mp hv2
    have hle12 : wisdomScore (WiseChoice s choices₁) ≤ wisdomScore (WiseChoice s choices₂) :=
      hmin1 _ h_in2'
    have hle21 : wisdomScore (WiseChoice s choices₂) ≤ wisdomScore (WiseChoice s choices₁) :=
      hmin2 _ h_in1'
    have heq : wisdomScore (WiseChoice s choices₁) = wisdomScore (WiseChoice s choices₂) :=
      le_antisymm hle12 hle21
    unfold wisdomScore at heq
    exact heq

private lemma wiseChoice_cons_eq_fold (s choice₀ : MoralState)
    (rest : List MoralState) :
    WiseChoice s (choice₀ :: rest) = rest.foldl wisdomStep choice₀ := by
  simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]

theorem wiseChoice_mem_of_ne_nil (s : MoralState)
    {choices : List MoralState} (h : choices ≠ []) :
    WiseChoice s choices ∈ choices := by
  cases choices with
  | nil => contradiction
  | cons c cs =>
    simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]
    have h_mem := wisdom_fold_mem cs c
    cases h_mem with
    | inl hfold_eq_c =>
      rw [hfold_eq_c]
      apply List.mem_cons.mpr
      left; rfl
    | inr hfold_mem =>
      apply List.mem_cons.mpr
      right; exact hfold_mem

theorem wisdom_prefers_sustainable
  (s : MoralState)
  (myopic long_term : MoralState)
  (h_future : (abs long_term.skew) < (abs myopic.skew)) :
  WiseChoice s [myopic, long_term] = long_term := by
  simp only [WiseChoice_cons, List.foldl_cons, List.foldl_nil, wisdomStep_self]
  unfold wisdomStep wisdomScore wisdomWeight
  have h_weight_pos : 0 < 1 / (1 + Foundation.φ) := wisdomWeight_pos
  have h_weighted_lt : (abs long_term.skew) * (1 / (1 + Foundation.φ)) <
      (abs myopic.skew) * (1 / (1 + Foundation.φ)) :=
    mul_lt_mul_of_pos_right h_future h_weight_pos
  simp only [h_weighted_lt, ↓reduceIte]

theorem wisdom_avoids_local_minima
  (s : MoralState)
  (prior future : List MoralState)
  (h_nonempty : prior ++ future ≠ [])
  (c : MoralState)
  (hc : c ∈ prior) :
  wisdomScore (WiseChoice s (prior ++ future)) ≤ wisdomScore c := by
  have h_mem : c ∈ prior ++ future := List.mem_append_left future hc
  exact wisdom_minimizes_longterm_skew s (prior ++ future) h_nonempty c h_mem

theorem wisdom_idempotent
  (s : MoralState)
  (choices : List MoralState) :
  let result := WiseChoice s choices
  WiseChoice result choices = result := by
  simp only
  cases choices with
  | nil =>
    rfl
  | cons c cs =>
    simp only [WiseChoice_cons, foldl_wisdomStep_cons_head]

theorem wisdom_concatenation
  (s : MoralState)
  (choices₁ choices₂ : List MoralState)
  (h₁ : choices₁ ≠ [])
  (h₂ : choices₂ ≠ []) :
  let result := WiseChoice s (choices₁ ++ choices₂)
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  (abs result.skew) * weight ≤
    min ((abs (WiseChoice s choices₁).skew) * weight)
        ((abs (WiseChoice s choices₂).skew) * weight) := by
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

theorem wisdom_iterative
  (s : MoralState)
  (step₁ step₂ : List MoralState)
  (h_step1_ne : step₁ ≠ [])
  (h_step2_ne : step₂ ≠ []) :
  let first := WiseChoice s step₁
  let second := WiseChoice first step₂
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  (abs (WiseChoice s (step₁ ++ step₂)).skew) * weight ≤
    (abs first.skew) * weight ∧
  (abs (WiseChoice s (step₁ ++ step₂)).skew) * weight ≤
    (abs second.skew) * weight := by
  simp only
  have h_ne : step₁ ++ step₂ ≠ [] := List.append_ne_nil_of_left_ne_nil h_step1_ne step₂
  have h_first_mem : WiseChoice s step₁ ∈ step₁ := wiseChoice_mem_of_ne_nil s h_step1_ne
  have h_second_mem : WiseChoice (WiseChoice s step₁) step₂ ∈ step₂ := wiseChoice_mem_of_ne_nil _ h_step2_ne
  have h_first_in_concat : WiseChoice s step₁ ∈ step₁ ++ step₂ := List.mem_append_left _ h_first_mem
  have h_second_in_concat : WiseChoice (WiseChoice s step₁) step₂ ∈ step₁ ++ step₂ :=
    List.mem_append_right _ h_second_mem
  constructor
  · have hle1 := wisdom_minimizes_longterm_skew s (step₁ ++ step₂) h_ne (WiseChoice s step₁) h_first_in_concat
    exact hle1
  · have hle2 := wisdom_minimizes_longterm_skew s (step₁ ++ step₂) h_ne (WiseChoice (WiseChoice s step₁) step₂) h_second_in_concat
    exact hle2

theorem wisdom_complements_love
  (s₁ s₂ : MoralState)
  (h_bal : (s₁.skew + s₂.skew) = 0) :
  let pair := Love s₁ s₂
  wisdomScore pair.1 = wisdomScore pair.2 := by
  unfold wisdomScore Love
  dsimp

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

theorem wisdom_respects_justice
  (protocol : JusticeProtocol)
  (entry : Entry)
  (h_balanced : entry.delta = 0)
  (s : MoralState)
  (choices : List MoralState) :
  WiseChoice (ApplyJustice protocol entry s)
    (choices.map (ApplyJustice protocol entry)) =
      ApplyJustice protocol entry (WiseChoice s choices) := by
  have h_score_preserve : ∀ m : MoralState,
      (ApplyJustice protocol entry m).skew = m.skew := by
    intro m
    unfold ApplyJustice
    simp only [h_balanced]
    norm_cast
    simp only [add_zero]
  exact wisdom_invariant_of_skew_preserving (ApplyJustice protocol entry) h_score_preserve s choices

theorem wisdom_phi_unique :
  let φ := Foundation.φ
  φ * φ = φ + 1 := by
  exact Support.GoldenRatio.phi_squared_eq_phi_plus_one

theorem wisdom_preserves_information :
  let φ := Foundation.φ
  let weight := 1 / (1 + φ)
  weight * φ * φ = 1 := by
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  have h_phi_sq : Foundation.φ * Foundation.φ = Foundation.φ + 1 := Support.GoldenRatio.phi_squared_eq_phi_plus_one
  field_simp [hφ_pos, h_phi_sq]
  linarith

theorem wisdom_temporal_dual_of_love
  (s₁ s₂ : MoralState) :
  let pair := Love s₁ s₂
  let total := s₁.energy + s₂.energy
  pair.2.energy / total = wisdomWeight := by
  simp only [Love, wisdomWeight]
  have h_total_pos : 0 < s₁.energy + s₂.energy := add_pos s₁.energy_pos s₂.energy_pos
  have hφ_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  field_simp [h_total_pos]
  ring

end Virtues
end Ethics
end IndisputableMonolith
