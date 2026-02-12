import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState

/-- Love equilibrates skew between two agents using φ-ratio energy distribution. -/
noncomputable def Love (s₁ s₂ : MoralState) : MoralState × MoralState :=
  let total_skew := s₁.skew + s₂.skew
  let σ_new := total_skew / 2
  let total_energy := s₁.energy + s₂.energy
  let φ := Foundation.φ
  let φ_ratio := φ / (1 + φ)

  let s₁' : MoralState := {
    ledger := s₁.ledger
    agent_bonds := s₁.agent_bonds
    skew := σ_new
    energy := total_energy * φ_ratio
    valid := s₁.valid
    energy_pos := by
      have hφ_pos : 0 < φ := Support.GoldenRatio.phi_pos
      have h_total_pos : 0 < total_energy := add_pos s₁.energy_pos s₂.energy_pos
      have h_ratio_pos : 0 < φ_ratio := by
        unfold φ_ratio
        apply div_pos hφ_pos
        linarith [Support.GoldenRatio.one_lt_phi]
      exact mul_pos h_total_pos h_ratio_pos
  }

  let s₂' : MoralState := {
    ledger := s₂.ledger
    agent_bonds := s₂.agent_bonds
    skew := σ_new
    energy := total_energy * (1 - φ_ratio)
    valid := s₂.valid
    energy_pos := by
      have hφ_pos : 0 < φ := Support.GoldenRatio.phi_pos
      have h_total_pos : 0 < total_energy := add_pos s₁.energy_pos s₂.energy_pos
      have h_one_minus_ratio_pos : 0 < 1 - φ_ratio := by
        unfold φ_ratio
        have h_denom_pos : 0 < 1 + φ := by linarith [Support.GoldenRatio.one_lt_phi]
        have h_lt : φ < 1 + φ := by linarith
        rw [sub_pos]
        exact (div_lt_one h_denom_pos).mpr h_lt
      exact mul_pos h_total_pos h_one_minus_ratio_pos
  }

  (s₁', s₂')

theorem love_conserves_skew (s₁ s₂ : MoralState) :
  (Love s₁ s₂).1.skew + (Love s₁ s₂).2.skew = s₁.skew + s₂.skew := by
  unfold Love
  dsimp
  ring

theorem love_conserves_energy (s₁ s₂ : MoralState) :
  (Love s₁ s₂).1.energy + (Love s₁ s₂).2.energy = s₁.energy + s₂.energy := by
  unfold Love
  dsimp
  ring

theorem love_reduces_variance (s₁ s₂ : MoralState) :
  abs ((Love s₁ s₂).1.skew - (Love s₁ s₂).2.skew) ≤ abs (s₁.skew - s₂.skew) := by
  unfold Love
  dsimp
  simp only [sub_self, abs_zero]
  exact abs_nonneg _

theorem love_creates_balance (s₁ s₂ : MoralState) :
  (Love s₁ s₂).1.skew = (Love s₁ s₂).2.skew := by
  unfold Love
  dsimp

theorem love_preserves_global_admissibility (s₁ s₂ : MoralState)
  (ha : globally_admissible [s₁, s₂]) :
  globally_admissible [(Love s₁ s₂).1, (Love s₁ s₂).2] := by
  unfold globally_admissible total_skew at *
  simp only [List.foldl_cons, List.foldl_nil, add_zero] at *
  linarith [love_conserves_skew s₁ s₂]

theorem love_minimizes_squared_skew (s₁ s₂ : MoralState) :
  ∀ (t₁ t₂ : ℝ), t₁ + t₂ = s₁.skew + s₂.skew →
    ((Love s₁ s₂).1.skew)^2 + ((Love s₁ s₂).2.skew)^2 ≤ t₁^2 + t₂^2 := by
  intro t1 t2 h_total
  unfold Love
  dsimp
  have : ((s₁.skew + s₂.skew) / 2) ^ 2 + ((s₁.skew + s₂.skew) / 2) ^ 2 = (s₁.skew + s₂.skew) ^ 2 / 2 := by ring
  rw [this]
  calc
    (s₁.skew + s₂.skew) ^ 2 / 2 = (t1 + t2) ^ 2 / 2 := by rw [h_total]
    _ = (t1 ^ 2 + 2 * t1 * t2 + t2 ^ 2) / 2 := by ring
    _ ≤ (t1 ^ 2 + (t1 ^ 2 + t2 ^ 2) + t2 ^ 2) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        linarith [two_mul_le_add_sq t1 t2]
    _ = t1 ^ 2 + t2 ^ 2 := by ring

theorem love_energy_split_is_golden (s₁ s₂ : MoralState) :
  (Love s₁ s₂).1.energy / (s₁.energy + s₂.energy) = 1 / Foundation.φ ∧
  (Love s₁ s₂).2.energy / (s₁.energy + s₂.energy) = 1 / (Foundation.φ * Foundation.φ) := by
  unfold Love
  dsimp
  have h_total_pos : s₁.energy + s₂.energy ≠ 0 := by
    have := add_pos s₁.energy_pos s₂.energy_pos
    exact ne_of_gt this
  constructor
  · field_simp [h_total_pos]
    exact Support.GoldenRatio.phi_ratio_identity
  · field_simp [h_total_pos]
    have h_phi_pos : 0 < Foundation.φ := Support.GoldenRatio.phi_pos
    have h_denom_ne : 1 + Foundation.φ ≠ 0 := by linarith
    have h1 : 1 - Foundation.φ / (1 + Foundation.φ) = 1 / (1 + Foundation.φ) := by
      field_simp [h_denom_ne]
      ring
    rw [h1]
    rw [Support.GoldenRatio.one_add_phi_eq_phi_sq]
    field_simp [h_phi_pos]

theorem love_symmetric (s₁ s₂ : MoralState) :
  (Love s₁ s₂).1.skew = (Love s₂ s₁).1.skew ∧
  (Love s₁ s₂).2.skew = (Love s₂ s₁).2.skew := by
  unfold Love
  dsimp
  constructor <;> ring

theorem love_idempotent_on_balanced (s₁ s₂ : MoralState)
  (h_bal : s₁.skew = s₂.skew) :
  (Love s₁ s₂).1.skew = s₁.skew ∧ (Love s₁ s₂).2.skew = s₂.skew := by
  unfold Love
  dsimp
  constructor <;> linarith

theorem love_reduces_imbalance (s₁ s₂ : MoralState) :
  max (abs (Love s₁ s₂).1.skew) (abs (Love s₁ s₂).2.skew) ≤
  max (abs s₁.skew) (abs s₂.skew) := by
  unfold Love
  dsimp
  simp only [max_self]
  rw [abs_div, abs_two]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h1 := abs_add_le s₁.skew s₂.skew
  have ha : abs s₁.skew ≤ max (abs s₁.skew) (abs s₂.skew) := le_max_left _ _
  have hb : abs s₂.skew ≤ max (abs s₁.skew) (abs s₂.skew) := le_max_right _ _
  linarith

theorem love_is_equilibration (s₁ s₂ : MoralState) :
  ∀ ε : ℝ, ((Love s₁ s₂).1.skew + ε) + ((Love s₁ s₂).2.skew - ε) = s₁.skew + s₂.skew := by
  intro ε
  unfold Love
  dsimp
  ring

end Virtues
end Ethics
end IndisputableMonolith
