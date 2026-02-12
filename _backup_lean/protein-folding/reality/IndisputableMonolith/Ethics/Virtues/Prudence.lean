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

Value(S) := E[|σ_future|] + λ · Var(|σ_future|)

where λ is risk-aversion parameter (higher λ → more conservative).

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
noncomputable def risk_adjusted_value (s : MoralState) (λ : ℝ) : ℝ :=
  (Int.natAbs s.skew : ℝ) + λ * variance_estimate s

/-- Selection step used by `PrudentChoice`. -/
private def prudenceStep (λ : ℝ) (best current : MoralState) : MoralState :=
  if risk_adjusted_value current λ < risk_adjusted_value best λ then current else best

/-- Prudent choice: select option minimizing risk-adjusted value.

This definition permits `λ = 0`, enabling direct comparison with
`WiseChoice` (pure expectation minimization) for compatibility proofs. The
semantic requirement `0 < λ` is enforced where needed rather than in the core
definition.
-/
noncomputable def PrudentChoice
  (s : MoralState)
  (choices : List MoralState)
  (λ : ℝ) :
  MoralState :=
  choices.foldl (prudenceStep λ) s

/-- Folding helper: the accumulated choice never has higher score than any processed element. -/
private lemma prudence_fold_step_min
    (λ : ℝ) (choices : List MoralState) (start : MoralState) :
    risk_adjusted_value (choices.foldl (prudenceStep λ) start) λ ≤ risk_adjusted_value start λ ∧
      ∀ c ∈ choices,
        risk_adjusted_value (choices.foldl (prudenceStep λ) start) λ ≤ risk_adjusted_value c λ := by
  refine List.recOn choices ?base ?step
  · intro start; simp [prudenceStep]
  · intro head tail ih start
    classical
    have hRec := ih (prudenceStep λ start head)
    rcases hRec with ⟨h_le_start, h_le_tail⟩
    by_cases hlt : risk_adjusted_value head λ < risk_adjusted_value start λ
    · have hwStep : prudenceStep λ start head = head := by simp [prudenceStep, hlt]
      have hFold_eq :
          tail.foldl (prudenceStep λ) (prudenceStep λ start head)
            = tail.foldl (prudenceStep λ) head := by simpa [hwStep]
      refine And.intro ?_ ?_
      · have h_le_head : risk_adjusted_value (tail.foldl (prudenceStep λ) head) λ ≤
          risk_adjusted_value head λ := by
          simpa [hwStep, hFold_eq] using h_le_start
        exact le_trans h_le_head (le_of_lt hlt)
      · intro c hc
        have hc' : c = head ∨ c ∈ tail := by simpa [List.mem_cons] using hc
        refine hc'.elim ?_ ?_
        · intro hcEq; subst hcEq
          have := h_le_start
          simpa [hwStep, hFold_eq]
        · intro hcTail
          have := h_le_tail c hcTail
          simpa [hwStep, hFold_eq] using this
    · have hwStep : prudenceStep λ start head = start := by simp [prudenceStep, hlt]
      have hFold_eq :
          tail.foldl (prudenceStep λ) (prudenceStep λ start head)
            = tail.foldl (prudenceStep λ) start := by simpa [hwStep]
      refine And.intro ?_ ?_
      · simpa [hwStep, hFold_eq] using h_le_start
      · intro c hc
        have hc' : c = head ∨ c ∈ tail := by simpa [List.mem_cons] using hc
        refine hc'.elim ?_ ?_
        · intro hcEq; subst hcEq
          have h_le_start' :
              risk_adjusted_value (tail.foldl (prudenceStep λ) start) λ ≤
                risk_adjusted_value start λ := by
            simpa [hwStep, hFold_eq] using h_le_start
          have h_start_le_head :
              risk_adjusted_value start λ ≤ risk_adjusted_value head λ :=
            le_of_not_lt hlt
          exact le_trans h_le_start' h_start_le_head
        · intro hcTail
          have := h_le_tail c hcTail
          simpa [hwStep, hFold_eq] using this

/-- The fold-based chooser always returns an element from the processed list. -/
private lemma prudence_fold_mem
    (λ : ℝ) (choices : List MoralState) (start : MoralState) :
    choices.foldl (prudenceStep λ) start = start ∨
      choices.foldl (prudenceStep λ) start ∈ choices := by
  refine List.recOn choices ?base ?step
  · intro start; left; simp [prudenceStep]
  · intro head tail ih start
    classical
    have hRec := ih (prudenceStep λ start head)
    by_cases hlt : risk_adjusted_value head λ < risk_adjusted_value start λ
    · have hwStep : prudenceStep λ start head = head := by simp [prudenceStep, hlt]
      have hFold_eq :
          tail.foldl (prudenceStep λ) (prudenceStep λ start head) =
            tail.foldl (prudenceStep λ) head := by simpa [hwStep]
      refine (hRec).elim ?_ ?_
      · intro hEq
        left
        simpa [hwStep, hFold_eq]
      · intro hMem
        right
        have : tail.foldl (prudenceStep λ) head ∈ tail := by
          simpa [hwStep, hFold_eq] using hMem
        exact List.mem_cons_of_mem _ this
    · have hwStep : prudenceStep λ start head = start := by simp [prudenceStep, hlt]
      have hFold_eq :
          tail.foldl (prudenceStep λ) (prudenceStep λ start head) =
            tail.foldl (prudenceStep λ) start := by simpa [hwStep]
      refine (ih start).elim ?_ ?_
      · intro hEq; left; simpa [hwStep, hFold_eq]
      · intro hMem
        right
        have : tail.foldl (prudenceStep λ) start ∈ tail := by
          simpa [hwStep, hFold_eq] using hMem
        exact List.mem_cons_of_mem _ this

/-! ## Core Theorems -/

/-- Prudence extends Wisdom (λ=0 case recovers Wisdom) -/
theorem prudence_extends_wisdom
  (s : MoralState)
  (choices : List MoralState) :
  -- When λ=0, prudence reduces to wisdom (no risk penalty)
  ∀ c ∈ choices, risk_adjusted_value c 0 = (Int.natAbs c.skew : ℝ) := by
  intro c h_mem
  unfold risk_adjusted_value variance_estimate
  simp

/-- With zero risk penalty, Prudence selects the smaller of
`s` and the wisdom-optimal choice by skew magnitude. -/
theorem prudence_zero_lambda_skew_min
  (s : MoralState)
  (choices : List MoralState)
  (h_nonempty : choices ≠ []) :
  let prudent := PrudentChoice s choices 0
  let wise := WiseChoice s choices
  (Int.natAbs prudent.skew : ℝ) =
    min ((Int.natAbs s.skew : ℝ)) (Int.natAbs wise.skew : ℝ) := by
  intro prudent wise
  classical
  have h_fold := prudence_fold_step_min 0 choices s
  have h_pr_le_s :
      (Int.natAbs prudent.skew : ℝ) ≤ (Int.natAbs s.skew : ℝ) := by
    simpa [PrudentChoice, prudent, risk_adjusted_value] using h_fold.1
  have h_cases : prudent = s ∨ prudent ∈ choices := by
    simpa [PrudentChoice, prudent] using prudence_fold_mem 0 choices s
  have h_wise_valid : wise = s ∨ wise ∈ choices := by
    simpa [wise] using Wisdom.wisdom_returns_valid_choice s choices
  have h_pr_le_wise :
      (Int.natAbs prudent.skew : ℝ) ≤ (Int.natAbs wise.skew : ℝ) := by
    cases h_wise_valid with
    | inl hEq =>
        simpa [wise, hEq] using h_pr_le_s
    | inr hMem =>
        simpa [PrudentChoice, prudent, wise, risk_adjusted_value]
          using h_fold.2 wise hMem
  refine le_antisymm ?h_le ?h_ge
  · exact le_min h_pr_le_s h_pr_le_wise
  · cases h_cases with
    | inl hEq =>
        subst hEq
        simpa using min_le_left ((Int.natAbs s.skew : ℝ)) (Int.natAbs wise.skew : ℝ)
    | inr hMem =>
        have h_weight_pos : 0 < (1 / (1 + Foundation.φ)) := by
          have hφ : 1 < Foundation.φ := Support.GoldenRatio.one_lt_phi
          have : 0 < 1 + Foundation.φ := by
            have : (0 : ℝ) < 1 := by norm_num
            linarith
          exact one_div_pos.mpr this
        have h_wisdom :=
          Wisdom.wisdom_minimizes_longterm_skew s choices h_nonempty
        have h_weighted :
            (Int.natAbs wise.skew : ℝ) * (1 / (1 + Foundation.φ)) ≤
              (Int.natAbs prudent.skew : ℝ) * (1 / (1 + Foundation.φ)) := by
          simpa [wise] using h_wisdom prudent hMem
        have h_weight_inv_nonneg : 0 ≤ (1 / (1 + Foundation.φ))⁻¹ :=
          le_of_lt (inv_pos.mpr h_weight_pos)
        have h_mul :=
          mul_le_mul_of_nonneg_left h_weighted h_weight_inv_nonneg
        have h_wise_le_prudent :
            (Int.natAbs wise.skew : ℝ) ≤ (Int.natAbs prudent.skew : ℝ) := by
          have h_ne : (1 / (1 + Foundation.φ)) ≠ 0 :=
            ne_of_gt h_weight_pos
          simpa [mul_comm, mul_left_comm, mul_assoc, h_ne, inv_mul_cancel,
            one_mul] using h_mul
        exact min_le_of_right_le h_wise_le_prudent

/-- Prudence minimizes the risk-adjusted value across the available choices. -/
theorem prudence_reduces_volatility
  (s : MoralState)
  (choices : List MoralState)
  (λ : ℝ)
  (h_lambda : 0 < λ) :
  let result := PrudentChoice s choices λ
  ∀ c ∈ s :: choices, risk_adjusted_value result λ ≤ risk_adjusted_value c λ := by
  intro result
  classical
  have h_fold := prudence_fold_step_min λ choices s
  have h_le_start := h_fold.1
  have h_le_choices := h_fold.2
  intro c hc

  have hc' : c = s ∨ c ∈ choices := by
    simpa [List.mem_cons] using hc
  refine hc'.elim ?_ ?_
  · intro hc_eq; subst hc_eq
    simpa [PrudentChoice, result] using h_le_start
  · intro hc_mem
    simpa [PrudentChoice, result] using h_le_choices c hc_mem

/-- The risk-adjusted value grows monotonically with λ. -/
theorem prudence_lambda_monotonic
  (s : MoralState)
  (λ₁ λ₂ : ℝ)
  (h_order : λ₁ ≤ λ₂) :
  risk_adjusted_value s λ₁ ≤ risk_adjusted_value s λ₂ := by
  have hVar_nonneg := variance_estimate_nonneg s
  unfold risk_adjusted_value
  exact add_le_add_left (mul_le_mul_of_nonneg_right h_order hVar_nonneg) _

/-- Small perturbations of λ change the prudent value by at most the variance penalty. -/
theorem prudence_increases_stability
  (s : MoralState)
  (choices : List MoralState)
  (λ : ℝ)
  (h_lambda : 0 < λ)
  (shock : ℝ)  -- External perturbation
  (h_shock_bounded : |shock| ≤ 1) :
  let result := PrudentChoice s choices λ
  |risk_adjusted_value result (λ + shock) - risk_adjusted_value result λ|
    ≤ variance_estimate result := by
  intro result
  classical
  set base := (Int.natAbs result.skew : ℝ) with hbase
  set var := variance_estimate result with hvar
  have hVar_nonneg : 0 ≤ var := by
    subst hvar
    exact variance_estimate_nonneg result
  have hDiff :
      risk_adjusted_value result (λ + shock) - risk_adjusted_value result λ =
        shock * var := by
    simp [risk_adjusted_value, hbase, hvar, mul_add, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
  have hAbs :
      |risk_adjusted_value result (λ + shock) - risk_adjusted_value result λ|
        = |shock| * var := by
    simpa [hDiff, abs_mul, abs_of_nonneg hVar_nonneg]
  have hBound := mul_le_mul_of_nonneg_right h_shock_bounded hVar_nonneg
  have hBound' : |shock| * var ≤ var := by
    simpa [mul_comm, one_mul] using hBound
  simpa [hAbs, hvar] using hBound'

/-- Sufficiently high λ shifts preference toward the lower-variance option. -/
theorem prudence_risk_reward_tradeoff
  (c₁ c₂ : MoralState)
  (h_c1_lower_expected : Int.natAbs c₁.skew < Int.natAbs c₂.skew)
  (h_c2_lower_variance : variance_estimate c₂ < variance_estimate c₁) :
  let threshold :=
    ((Int.natAbs c₂.skew : ℝ) - (Int.natAbs c₁.skew : ℝ)) /
      (variance_estimate c₁ - variance_estimate c₂)
  in ∀ {λ : ℝ}, threshold ≤ λ →
      risk_adjusted_value c₂ λ ≤ risk_adjusted_value c₁ λ := by
  intro threshold λ hλ
  classical
  set abs₁ := (Int.natAbs c₁.skew : ℝ) with habs₁
  set abs₂ := (Int.natAbs c₂.skew : ℝ) with habs₂
  set var₁ := variance_estimate c₁ with hvar₁
  set var₂ := variance_estimate c₂ with hvar₂
  have hAbs_lt : abs₁ < abs₂ := by
    have := (by exact_mod_cast h_c1_lower_expected
      : (Int.natAbs c₁.skew : ℝ) < (Int.natAbs c₂.skew : ℝ))
    simpa [habs₁, habs₂]
  have hVar_lt : var₂ < var₁ := by
    simpa [hvar₁, hvar₂] using h_c2_lower_variance
  have hVar_pos : 0 < var₁ - var₂ := sub_pos.mpr hVar_lt
  have hDenom_ne : var₁ - var₂ ≠ 0 := ne_of_gt hVar_pos
  have hScaled : abs₂ - abs₁ ≤ λ * (var₁ - var₂) := by
    have :=
      mul_le_mul_of_nonneg_right (by simpa [threshold, hvar₁, hvar₂, habs₁, habs₂] using hλ)
        (le_of_lt hVar_pos)
    simpa [threshold, hvar₁, hvar₂, habs₁, habs₂, hDenom_ne, mul_comm, mul_left_comm,
      mul_assoc] using this
  have hNonneg :
      0 ≤ risk_adjusted_value c₁ λ - risk_adjusted_value c₂ λ := by
    have hDiff :
        risk_adjusted_value c₁ λ - risk_adjusted_value c₂ λ =
          λ * (var₁ - var₂) - (abs₂ - abs₁) := by
      simp [risk_adjusted_value, hvar₁, hvar₂, habs₁, habs₂, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
    have : 0 ≤ λ * (var₁ - var₂) - (abs₂ - abs₁) := sub_nonneg.mpr hScaled
    simpa [hDiff]
  exact sub_nonneg.mp hNonneg

/-! ## Compositional Properties -/

/-- Prudence is more conservative than Wisdom -/
theorem prudence_more_conservative_than_wisdom
  (s : MoralState)
  (choices : List MoralState)
  (λ : ℝ)
  (h_lambda : 0 < λ)
  (risky_choice safe_choice : MoralState)
  (h_risky_in : risky_choice ∈ choices)
  (h_safe_in : safe_choice ∈ choices)
  (h_risky_lower : Int.natAbs risky_choice.skew < Int.natAbs safe_choice.skew)
  (h_risky_volatile : variance_estimate risky_choice > variance_estimate safe_choice)
  (h_penalty :
      (Int.natAbs safe_choice.skew : ℝ) - (Int.natAbs risky_choice.skew : ℝ)
        ≤ λ * (variance_estimate risky_choice - variance_estimate safe_choice)) :
  let result := PrudentChoice s choices λ
  risk_adjusted_value result λ ≤ risk_adjusted_value safe_choice λ := by
  intro result
  classical
  have hSafeBetter :
      risk_adjusted_value safe_choice λ ≤ risk_adjusted_value risky_choice λ := by
    set absSafe := (Int.natAbs safe_choice.skew : ℝ) with hAbsSafe
    set absRisky := (Int.natAbs risky_choice.skew : ℝ) with hAbsRisky
    set varSafe := variance_estimate safe_choice with hVarSafe
    set varRisky := variance_estimate risky_choice with hVarRisky
    have hineq : absSafe - absRisky ≤ λ * (varRisky - varSafe) := by
      simpa [hAbsSafe, hAbsRisky, hVarSafe, hVarRisky] using h_penalty
    have hDiff :
        risk_adjusted_value risky_choice λ - risk_adjusted_value safe_choice λ =
          λ * (varRisky - varSafe) - (absSafe - absRisky) := by
      simp [risk_adjusted_value, hAbsSafe, hAbsRisky, hVarSafe, hVarRisky, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_comm, mul_left_comm,
        mul_assoc]
    have : 0 ≤ risk_adjusted_value risky_choice λ - risk_adjusted_value safe_choice λ := by
      have := sub_nonneg.mpr hineq
      simpa [hDiff]
    exact sub_nonneg.mp this
  have hMinimal := prudence_reduces_volatility s choices λ h_lambda
  have hSafe_mem : safe_choice ∈ s :: choices := by
    exact List.mem_cons_of_mem _ h_safe_in
  have hResult_le_safe := hMinimal safe_choice hSafe_mem
  exact le_trans hResult_le_safe hSafeBetter

/-- Prudence converges to deterministic choice as uncertainty resolves -/
theorem prudence_converges_to_wisdom
  (s : MoralState)
  (choices : List MoralState)
  (λ : ℝ)
  (h_lambda : 0 < λ)
  (h_all_low_var : ∀ c ∈ s :: choices, variance_estimate c ≤ 0.01) :
  let result := PrudentChoice s choices λ
  risk_adjusted_value result λ - (Int.natAbs result.skew : ℝ) ≤ λ * 0.01 := by
  intro result
  classical
  have hMem : result = s ∨ result ∈ choices := by
    simpa [PrudentChoice, result] using prudence_fold_mem λ choices s
  have hResult_mem : result ∈ s :: choices := by
    cases hMem with
    | inl hEq => simpa [hEq] using List.mem_cons_self s choices
    | inr hIn => exact List.mem_cons_of_mem _ hIn
  have hVar_bound : variance_estimate result ≤ 0.01 :=
    h_all_low_var result hResult_mem
  have hλ_nonneg : 0 ≤ λ := le_of_lt h_lambda
  have hExpr :
      risk_adjusted_value result λ - (Int.natAbs result.skew : ℝ)
        = λ * variance_estimate result := by
    simp [risk_adjusted_value]
  have : λ * variance_estimate result ≤ λ * 0.01 :=
    mul_le_mul_of_nonneg_left hVar_bound hλ_nonneg
  simpa [hExpr]

/-! ## Ethical Interpretation -/

/-- Prudence protects against unforeseen shocks -/
theorem prudence_protects_against_shocks
  (s : MoralState)
  (choices : List MoralState)
  (λ : ℝ)
  (h_lambda : 0 < λ)
  (shock : ℝ)
  (h_shock_bounded : |shock| ≤ 1) :
  let result := PrudentChoice s choices λ
  risk_adjusted_value result (λ + shock) ≥
    risk_adjusted_value result λ - variance_estimate result := by
  intro result
  classical
  set var := variance_estimate result with hvar
  have hVar_nonneg : 0 ≤ var := by
    subst hvar; exact variance_estimate_nonneg result
  have hBounds := abs_le.mp h_shock_bounded
  have hLower : -1 ≤ shock := hBounds.1
  have hLinear :
      risk_adjusted_value result (λ + shock) =
        risk_adjusted_value result λ + shock * var := by
    simp [risk_adjusted_value, hvar, mul_add, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]
  have hLowerMul : -var ≤ shock * var := by
    have := mul_le_mul_of_nonneg_right hLower hVar_nonneg
    simpa [mul_comm, hvar] using this
  have :
      risk_adjusted_value result λ - variance_estimate result
        = risk_adjusted_value result λ + (-var) := by
    simp [hvar, sub_eq_add_neg]
  calc
    risk_adjusted_value result (λ + shock)
        = risk_adjusted_value result λ + shock * var := hLinear
    _ ≥ risk_adjusted_value result λ + (-var) := by
          exact add_le_add_left hLowerMul _
    _ = risk_adjusted_value result λ - variance_estimate result := by
          simpa [hvar, sub_eq_add_neg]

/-- Prudence is wisdom + robustness -/
theorem prudence_is_robust_wisdom :
  ∀ s : MoralState, ∀ λ : ℝ,
    risk_adjusted_value s λ = risk_adjusted_value s 0 + λ * variance_estimate s := by
  intro s λ; simp [risk_adjusted_value, add_comm, add_left_comm, add_assoc]

/-- Prudence value function is convex in λ -/
theorem prudence_convex_in_lambda
  (s : MoralState)
  (λ₁ λ₂ : ℝ)
  (α : ℝ) (h_α : 0 ≤ α ∧ α ≤ 1) :
  let λ := α * λ₁ + (1 - α) * λ₂
  -- Risk-adjusted value is convex in λ
  risk_adjusted_value s λ ≤
    α * risk_adjusted_value s λ₁ + (1 - α) * risk_adjusted_value s λ₂ := by
  intro λ
  have hEq :
      risk_adjusted_value s λ =
        α * risk_adjusted_value s λ₁ + (1 - α) * risk_adjusted_value s λ₂ := by
    simp [risk_adjusted_value, λ, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]
  exact hEq.le

/--
TODO:
- Replace the threshold-style hypotheses with quantitative bounds exported by
  `ValueFunctional` and `Harm` once the zero-parameter variance certificates
  land (the current `variance_estimate` proxy should be swapped for the
  probability-backed helper likely living alongside
  `BiophaseIntegration.AcceptanceCriteria`).
- Capture tie-breaking guarantees so that the zero-λ corollary can conclude
  `PrudentChoice = WiseChoice` when Wisdom strictly improves on `s`.
- Thread the consent/ΔS machinery once the harm/value interfaces finish
  exposing their directional derivative certificates.
-/

end Virtues
end Ethics
end IndisputableMonolith
