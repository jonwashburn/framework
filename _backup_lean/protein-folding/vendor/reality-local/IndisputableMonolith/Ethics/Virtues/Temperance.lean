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
  have h5 : (0 : ℝ) < 5 := by norm_num
  have hsqrt5 : 2 < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- 1/φ is less than 1 -/
theorem inv_phi_lt_one : 1 / Foundation.φ < 1 := by
  have hphi_pos : 0 < Foundation.φ := by
    unfold Foundation.φ
    have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  rw [div_lt_one hphi_pos]
  exact phi_gt_one

/-- Temperance prevents energy collapse -/
theorem temperance_prevents_collapse
  (s s' : MoralState)
  (E_total : ℝ)
  (h_temperate : TemperateTransition s s' E_total)
  (h_positive : 0 < E_total)
  (h_s_energy : s.energy ≤ E_total) :
  0 < s'.energy := by
  -- s' has positive energy from its structure
  exact s'.energy_pos

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
  -- The identity 1/c + 1/c² = 1 is equivalent to c² = c + 1
  -- which is the defining equation for φ
  have hc_pos : 0 < c := by linarith
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hcc_ne : c * c ≠ 0 := mul_ne_zero hc_ne hc_ne
  -- From 1/c + 1/c² = 1, multiply by c² to get c + 1 = c²
  have h_eq : c + 1 = c * c := by
    field_simp [hc_ne, hcc_ne] at h_identity
    linarith
  -- φ satisfies the same equation: φ² = φ + 1
  have h_phi_eq : Foundation.φ * Foundation.φ = Foundation.φ + 1 := Support.GoldenRatio.phi_squared_eq_phi_plus_one
  -- c satisfies c² = c + 1 (from h_eq: c + 1 = c²)
  have h_c_eq : c * c = c + 1 := h_eq.symm
  -- Both c and φ satisfy x² - x - 1 = 0, and both > 1
  -- The unique positive root > 1 is (1 + √5)/2 = φ
  have h_phi_gt_one : 1 < Foundation.φ := Support.GoldenRatio.one_lt_phi
  -- c and φ both satisfy the same quadratic and are both > 1
  -- Quadratic x² - x - 1 = 0 has roots (1 ± √5)/2
  -- Only (1 + √5)/2 > 1, so c = φ
  have h_c_sub : c * c - c - 1 = 0 := by linarith
  have h_phi_sub : Foundation.φ * Foundation.φ - Foundation.φ - 1 = 0 := by linarith [h_phi_eq]
  -- Use that the quadratic has exactly two roots and only one is > 1
  nlinarith [sq_nonneg (c - Foundation.φ), sq_nonneg c, sq_nonneg Foundation.φ,
             Support.GoldenRatio.phi_pos, h_c_sub, h_phi_sub]

/-- A temperate transformation preserves energy positivity for every state respecting the total budget. -/
theorem temperance_applies_universally
  (transformation : MoralState → MoralState)
  (E_total : ℝ)
  (h_temperate : ∀ s, TemperateTransition s (transformation s) E_total)
  (h_positive : 0 < E_total)
  (h_bound : ∀ (s : MoralState), s.energy ≤ E_total) :
  ∀ s, 0 < (ApplyTemperance s E_total transformation (h_temperate s)).energy := by
  intro s
  exact temperance_preserves_viability s E_total transformation (h_temperate s) h_positive (h_bound s)

/-- A uniformly intemperate transformation consumes the available energy budget in finitely many steps. -/
theorem intemperate_leads_to_depletion
  (s : MoralState)
  (transformation : MoralState → MoralState)
  (E_total : ℝ)
  (h_bound : s.energy ≤ E_total)
  (h_positive : 0 < E_total)
  (h_intemperate : ∀ s', (transformation s').energy ≤ s'.energy - E_total / Foundation.φ) :
  ∃ n : ℕ, (Nat.iterate transformation n s).energy ≤ 0 := by
  -- Each step decreases energy by at least E_total/φ
  -- After ⌈φ⌉ + 1 steps, energy ≤ E_total - (⌈φ⌉ + 1) * E_total/φ ≤ 0
  have hphi_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
  have hdelta_pos : 0 < E_total / Foundation.φ := div_pos h_positive hphi_pos
  -- Use ceiling of φ as bound
  let n := Nat.ceil Foundation.φ + 1
  use n
  -- After n iterations, energy decreases by at least n * E_total / φ
  -- We prove by induction that after k steps, energy ≤ s.energy - k * (E_total / φ)
  have h_iter_bound : ∀ k : ℕ, (Nat.iterate transformation k s).energy ≤ s.energy - k * (E_total / Foundation.φ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      calc (transformation (Nat.iterate transformation k s)).energy
        ≤ (Nat.iterate transformation k s).energy - E_total / Foundation.φ := h_intemperate _
        _ ≤ (s.energy - k * (E_total / Foundation.φ)) - E_total / Foundation.φ := by linarith
        _ = s.energy - (k + 1 : ℕ) * (E_total / Foundation.φ) := by push_cast; ring
  -- Now apply with k = n
  calc (Nat.iterate transformation n s).energy
    ≤ s.energy - n * (E_total / Foundation.φ) := h_iter_bound n
    _ ≤ E_total - n * (E_total / Foundation.φ) := by linarith
    _ = E_total * (1 - n / Foundation.φ) := by ring
    _ ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_positive)
      -- Need: 1 - n / φ ≤ 0, i.e., n / φ ≥ 1, i.e., n ≥ φ
      -- n = ⌈φ⌉ + 1 ≥ φ + 1 - 1 = φ (since ⌈φ⌉ ≥ φ)
      have h_ceil_ge : (Nat.ceil Foundation.φ : ℝ) ≥ Foundation.φ := Nat.le_ceil Foundation.φ
      have h_n_ge_phi : (n : ℝ) ≥ Foundation.φ := by
        simp only [n]
        have h1 : (↑(Nat.ceil Foundation.φ + 1) : ℝ) = (Nat.ceil Foundation.φ : ℝ) + 1 := by
          push_cast; ring
        rw [h1]
        linarith
      rw [sub_nonpos]
      have h_div : n / Foundation.φ ≥ 1 := by
        rw [ge_iff_le, one_le_div hphi_pos]
        exact h_n_ge_phi
      linarith

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
  induction states generalizing s₀ with
  | nil =>
    simp [followChain]
  | cons s₁ rest ih =>
    simp only [followChain, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h_first : TemperateTransition s₀ s₁ E_total := by
      cases h_chain; assumption
    have h_rest : List.Chain (fun s₁ s₂ => TemperateTransition s₁ s₂ E_total) s₁ rest := by
      cases h_chain; assumption
    have ih_applied := ih s₁ h_rest
    unfold TemperateTransition at h_first
    calc |(followChain s₁ rest).energy - s₀.energy|
        ≤ |(followChain s₁ rest).energy - s₁.energy| + |s₁.energy - s₀.energy| := abs_sub_le _ _ _
      _ ≤ (rest.length : ℝ) * (E_total / Foundation.φ) + E_total / Foundation.φ := by linarith
      _ = (rest.length + 1 : ℝ) * (E_total / Foundation.φ) := by ring

end Virtues
end Ethics
end IndisputableMonolith
