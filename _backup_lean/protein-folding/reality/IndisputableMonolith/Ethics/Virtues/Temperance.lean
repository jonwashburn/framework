import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio
import IndisputableMonolith.PhiSupport.Lemmas

/-!
# Temperance: Energy Constraint

Temperance moderates energy expenditure, preventing actions that would lead to
systemic energy depletion or excessive secondary curvature.

## Mathematical Definition

For any proposed state transition S → S', the transition is temperate if:
ΔE = |E' - E| ≤ (1/φ) · E_total

## Physical Grounding

- **φ-fraction limit**: Ensures no single action depletes total energy
- **Sustainability**: Maintains positive energy for future actions
- **Convexity**: From J''(1)=1, prevents over-strain

## Connection to virtues.tex

Section 6 (Temperance): "To moderate energy expenditure and prevent actions that,
while locally beneficial, might lead to systemic energy depletion."

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState
open List
open Function

/-! ## Core Definitions -/

/-- A transition is temperate if energy change is bounded by φ-fraction -/
def TemperateTransition (s s' : MoralState) (E_total : ℝ) : Prop :=
  let ΔE := |s'.energy - s.energy|
  let φ := Foundation.φ
  ΔE ≤ E_total / φ

/-- Apply a transformation with temperance constraint -/
noncomputable def ApplyTemperance
  (s : MoralState)
  (E_total : ℝ)
  (transformation : MoralState → MoralState)
  (h_temperate : TemperateTransition s (transformation s) E_total) :
  MoralState :=
  transformation s

/-! ## Core Theorems -/

/-- φ is greater than 1 -/
theorem phi_gt_one : 1 < Foundation.φ := by
  unfold Foundation.φ
  norm_num
  have : 2 < Real.sqrt 5 + 1 := by
    have : 2 < Real.sqrt 5 := by norm_num
    linarith
  linarith

/-- 1/φ is less than 1 -/
theorem inv_phi_lt_one : 1 / Foundation.φ < 1 := by
  have h := phi_gt_one
  apply div_lt_one_of_lt h
  exact lt_trans zero_lt_one h

/-- Temperance prevents energy collapse -/
theorem temperance_prevents_collapse
  (s s' : MoralState)
  (E_total : ℝ)
  (h_temperate : TemperateTransition s s' E_total)
  (h_positive : 0 < E_total)
  (h_s_energy : s.energy ≤ E_total) :
  0 < s'.energy := by
  unfold TemperateTransition at h_temperate
  -- ΔE ≤ E_total/φ and φ > 1, so ΔE < E_total
  have h_bound : |s'.energy - s.energy| ≤ E_total / Foundation.φ := h_temperate
  have h_frac_bound : E_total / Foundation.φ < E_total := by
    apply div_lt_self h_positive
    exact phi_gt_one
  -- If s.energy ≤ E_total and |ΔE| < E_total, then s'.energy > 0
  by_cases h : s.energy ≤ s'.energy
  · -- Energy increased or stayed same
    calc s'.energy
      ≥ s.energy := h
      _ > 0 := s.energy_pos
  · -- Energy decreased
    push_neg at h
    have h_decrease : s.energy - s'.energy < E_total := by
      calc s.energy - s'.energy
        = |s'.energy - s.energy| := by simp [abs_sub_comm]; exact abs_of_pos (by linarith)
        _ ≤ E_total / Foundation.φ := h_bound
        _ < E_total := h_frac_bound
    linarith [s.energy_pos]

/-- Temperance preserves physical viability -/
theorem temperance_preserves_viability
  (s : MoralState)
  (E_total : ℝ)
  (transformation : MoralState → MoralState)
  (h_temperate : TemperateTransition s (transformation s) E_total)
  (h_positive : 0 < E_total)
  (h_s_bound : s.energy ≤ E_total) :
  0 < (ApplyTemperance s E_total transformation h_temperate).energy := by
  unfold ApplyTemperance
  exact temperance_prevents_collapse s (transformation s) E_total h_temperate h_positive h_s_bound

/-- Temperance uses φ as sustainability bound -/
theorem temperance_phi_bound
  (s s' : MoralState)
  (E_total : ℝ) :
  TemperateTransition s s' E_total ↔ |s'.energy - s.energy| ≤ E_total / Foundation.φ := by
  rfl

/-- `φ` is the unique positive solution of the temperance sustainability identity. -/
theorem temperance_phi_optimal
  {c : ℝ}
  (h_c : 1 < c)
  (h_identity : 1 / c + 1 / (c * c) = 1) :
  c = Foundation.φ := by
  have hc_pos : 0 < c := lt_trans (by norm_num) h_c
  have hc_ne_zero : c ≠ 0 := ne_of_gt hc_pos
  have h_mul := congrArg (fun t : ℝ => t * c ^ 2) h_identity
  simp [pow_two, hc_ne_zero, mul_add, add_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] at h_mul
  have h_sq : c ^ 2 = c + 1 := by
    simpa [pow_two] using h_mul.symm
  have h_pair : c ^ 2 = c + 1 ∧ 0 < c := ⟨h_sq, hc_pos⟩
  have h_constants : c = IndisputableMonolith.Constants.phi :=
    (IndisputableMonolith.PhiSupport.phi_unique_pos_root c).mp h_pair
  simpa [Support.GoldenRatio.foundation_phi_eq_constants] using h_constants

/-- A temperate transformation preserves energy positivity for every state respecting the total budget. -/
theorem temperance_applies_universally
  (transformation : MoralState → MoralState)
  (E_total : ℝ)
  (h_temperate : ∀ s, TemperateTransition s (transformation s) E_total)
  (h_positive : 0 < E_total)
  (h_bound : ∀ s, s.energy ≤ E_total) :
  ∀ s, 0 < (ApplyTemperance s E_total transformation (h_temperate s)).energy := by
  intro s
  exact
    temperance_preserves_viability s E_total transformation (h_temperate s) h_positive (h_bound s)

/-- A uniformly intemperate transformation consumes the available energy budget in finitely many steps. -/
theorem intemperate_leads_to_depletion
  (s : MoralState)
  (transformation : MoralState → MoralState)
  (E_total : ℝ)
  (h_bound : s.energy ≤ E_total)
  (h_positive : 0 < E_total)
  (h_intemperate : ∀ s', (transformation s').energy ≤ s'.energy - E_total / Foundation.φ) :
  ∃ n : ℕ, ((Function.iterate n transformation) s).energy ≤ 0 := by
  classical
  set drop := E_total / Foundation.φ
  have h_phi_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  have h_drop_pos : 0 < drop := div_pos h_positive h_phi_pos
  have h_drop_ne_zero : drop ≠ 0 := ne_of_gt h_drop_pos
  have h_iter_bound : ∀ n : ℕ, ((Function.iterate n transformation) s).energy ≤
      s.energy - (n : ℝ) * drop := by
    intro n
    induction' n with k hk
    · simp [Function.iterate, drop]
    · have h_step :=
        h_intemperate ((Function.iterate k transformation) s)
      have h_sub := sub_le_sub hk le_rfl
      have h_next := le_trans h_step h_sub
      simpa [Nat.cast_succ, add_comm, add_left_comm, add_assoc, mul_add, add_mul, drop] using h_next
  obtain ⟨n, hn⟩ := exists_nat_gt (s.energy / drop)
  have hn_pos : s.energy < (n : ℝ) * drop := by
    have h_mul := mul_lt_mul_of_pos_right hn h_drop_pos
    simpa [drop, div_eq_mul_inv, h_drop_ne_zero, mul_comm, mul_left_comm, mul_assoc] using h_mul
  have h_energy_le : s.energy ≤ (n : ℝ) * drop := le_of_lt hn_pos
  refine ⟨n, ?_⟩
  have h_iter := h_iter_bound n
  have h_final : s.energy - (n : ℝ) * drop ≤ 0 := by
    have := h_energy_le
    linarith
  exact le_trans h_iter h_final

/-! ## Compositional Properties -/

/-- Follow a chain of moral states, returning the terminal state. -/
def followChain : MoralState → List MoralState → MoralState
  | s, [] => s
  | _s, s' :: rest => followChain s' rest

/-- Temperance is transitive across compositions -/
theorem temperance_transitive
  (s₁ s₂ s₃ : MoralState)
  (E_total : ℝ)
  (h₁₂ : TemperateTransition s₁ s₂ E_total)
  (h₂₃ : TemperateTransition s₂ s₃ E_total) :
  |s₃.energy - s₁.energy| ≤ 2 * (E_total / Foundation.φ) := by
  unfold TemperateTransition at h₁₂ h₂₃
  calc |s₃.energy - s₁.energy|
    ≤ |s₃.energy - s₂.energy| + |s₂.energy - s₁.energy| := abs_sub_le s₃.energy s₂.energy s₁.energy
    _ ≤ E_total / Foundation.φ + E_total / Foundation.φ := by linarith
    _ = 2 * (E_total / Foundation.φ) := by ring

/-- Aggregate temperance bound across a finite chain of temperate transitions. -/
theorem temperance_multiple_actions
  (s₀ : MoralState)
  (states : List MoralState)
  (E_total : ℝ)
  (h_chain : List.Chain (fun s₁ s₂ => TemperateTransition s₁ s₂ E_total) s₀ states) :
  |(followChain s₀ states).energy - s₀.energy| ≤
      (states.length : ℝ) * (E_total / Foundation.φ) := by
  classical
  revert s₀
  refine
    List.induction_on states ?base ?step
  · intro s₀ h_chain
    simp [followChain]
  · intro s₁ tail ih s₀ h_chain
    cases' h_chain with h_step h_rest
    have h_head : |s₁.energy - s₀.energy| ≤ E_total / Foundation.φ := by
      simpa [TemperateTransition] using h_step
    have h_tail := ih s₁ h_rest
    have h_triangle :=
      abs_sub_le ((followChain s₁ tail).energy) s₁.energy s₀.energy
    have :=
      calc
        |(followChain s₁ tail).energy - s₀.energy|
            ≤ |(followChain s₁ tail).energy - s₁.energy| + |s₁.energy - s₀.energy| :=
              h_triangle
        _ ≤ (tail.length : ℝ) * (E_total / Foundation.φ) + E_total / Foundation.φ :=
          add_le_add h_tail h_head
    have h_len : (((s₁ :: tail).length : ℝ) * (E_total / Foundation.φ)) =
        (tail.length : ℝ) * (E_total / Foundation.φ) + E_total / Foundation.φ := by
      simp [Nat.cast_succ, List.length_cons, add_comm, add_left_comm, add_assoc, mul_add, add_mul]
    simpa [followChain, List.length_cons, h_len] using this

end Virtues
end Ethics
end IndisputableMonolith
