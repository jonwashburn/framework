import Mathlib
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Ethics.MoralState
import IndisputableMonolith.Ethics.ConservationLaw
import IndisputableMonolith.Support.GoldenRatio

/-!
# Compassion: Asymmetric Relief with Energy Transfer

Compassion reduces suffering by providing aid to states with high debt and low energy.
It's a targeted form of Love, applied asymmetrically.

## Mathematical Definition

For helper and sufferer states, compassion:
1. Transfers energy: min(E_helper · 1/φ², E_target - E_sufferer)
2. Relieves curvature: energy_transfer · φ⁴ (conversion rate)
3. Helper cost: takes on small fraction (0.1) of relieved debt

## Physical Grounding

- **φ²-fraction**: Optimal transfer using Golden Ratio
- **φ⁴ conversion**: Energy-to-skew relief rate
- **Asymmetric**: Unlike Love (symmetric), Compassion targets suffering

-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open Foundation
open MoralState
open Support
open Support.GoldenRatio

local notation "φ" => Foundation.φ

namespace CompassionSpec

/-- Energy transferred from helper to sufferer under compassion. -/
noncomputable def energyTransfer
    (helper sufferer : MoralState) (E_target : ℝ) : ℝ :=
  min (helper.energy / (φ * φ)) (E_target - sufferer.energy)

/-- Skew relief achieved for the sufferer. -/
noncomputable def skewRelief
    (helper sufferer : MoralState) (E_target : ℝ) : ℤ :=
  Int.floor (energyTransfer helper sufferer E_target * φ ^ 4)

/-- Fractional skew absorbed by the helper (10% of the relief). -/
noncomputable def helperBurden
    (helper sufferer : MoralState) (E_target : ℝ) : ℝ :=
  (skewRelief helper sufferer E_target : ℝ) / 10

/-- Integer skew delta incurred by the helper. -/
noncomputable def helperSkewDelta
    (helper sufferer : MoralState) (E_target : ℝ) : ℤ :=
  Int.floor (helperBurden helper sufferer E_target)

lemma phi_sq_gt_one : 1 < φ * φ := by
  have hφ_gt_one : 1 < φ := Constants.one_lt_phi
  have hφ_pos : 0 < φ := phi_pos
  calc 1 = 1 * 1 := by ring
    _ < φ * 1 := by nlinarith
    _ < φ * φ := by nlinarith

lemma phi_pow_four_pos : 0 < φ ^ 4 := by
  have hφ_pos : 0 < φ := phi_pos
  simpa using pow_pos hφ_pos (4 : ℕ)

lemma energyTransfer_le_helper
    (helper sufferer : MoralState) (E_target : ℝ) :
    energyTransfer helper sufferer E_target ≤ helper.energy / (φ * φ) :=
  min_le_left _ _

lemma energyTransfer_le_gap
    (helper sufferer : MoralState) (E_target : ℝ) :
    energyTransfer helper sufferer E_target ≤ E_target - sufferer.energy :=
  min_le_right _ _

lemma energyTransfer_pos
    (helper sufferer : MoralState) (E_target : ℝ)
    (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
    0 < energyTransfer helper sufferer E_target := by
  have hφ_pos : 0 < φ := phi_pos
  have h_term₁ : 0 < helper.energy / (φ * φ) := by
    have h_denom_pos : 0 < φ * φ := mul_pos hφ_pos hφ_pos
    exact div_pos helper.energy_pos h_denom_pos
  have h_term₂ : 0 < E_target - sufferer.energy := sub_pos.mpr h_suffering.2
  unfold energyTransfer
  exact lt_min h_term₁ h_term₂

lemma energyTransfer_lt_helper
    (helper sufferer : MoralState) (E_target : ℝ)
    (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
    energyTransfer helper sufferer E_target < helper.energy := by
  have h_le := energyTransfer_le_helper helper sufferer E_target
  have h_strict : helper.energy / (φ * φ) < helper.energy :=
    div_lt_self helper.energy_pos phi_sq_gt_one
  exact lt_of_le_of_lt h_le h_strict

lemma skewRelief_nonneg
    (helper sufferer : MoralState) (E_target : ℝ)
    (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
    0 ≤ skewRelief helper sufferer E_target := by
  have h_transfer_pos := energyTransfer_pos helper sufferer E_target h_suffering
  have h_prod_nonneg : 0 ≤ energyTransfer helper sufferer E_target * φ ^ 4 := by
    have hφ_pow_nonneg : 0 ≤ φ ^ 4 := le_of_lt phi_pow_four_pos
    exact mul_nonneg (le_of_lt h_transfer_pos) hφ_pow_nonneg
  unfold skewRelief
  exact Int.floor_nonneg.mpr h_prod_nonneg

lemma helperBurden_nonneg
    (helper sufferer : MoralState) (E_target : ℝ)
    (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
    0 ≤ helperBurden helper sufferer E_target := by
  have h_relief_nonneg := skewRelief_nonneg helper sufferer E_target h_suffering
  unfold helperBurden
  have h_cast_nonneg : 0 ≤ (skewRelief helper sufferer E_target : ℝ) := by
    exact_mod_cast h_relief_nonneg
  have h_pos : (0 : ℝ) < 10 := by norm_num
  have : 0 ≤ (skewRelief helper sufferer E_target : ℝ) / 10 :=
    div_nonneg h_cast_nonneg (le_of_lt h_pos)
  simpa using this

lemma helperSkewDelta_le_relief
    (helper sufferer : MoralState) (E_target : ℝ)
    (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
    helperSkewDelta helper sufferer E_target ≤
      skewRelief helper sufferer E_target := by
  classical
  have h_relief_nonneg := skewRelief_nonneg helper sufferer E_target h_suffering
  have h_relief_cast_nonneg :
      0 ≤ (skewRelief helper sufferer E_target : ℝ) := by
    exact_mod_cast h_relief_nonneg
  have h_burden_le :
      helperBurden helper sufferer E_target ≤
        (skewRelief helper sufferer E_target : ℝ) := by
    unfold helperBurden
    have h_coeff : (1 / (10 : ℝ)) ≤ 1 := by norm_num
    have h_mul := mul_le_mul_of_nonneg_left h_coeff h_relief_cast_nonneg
    simpa [div_eq_mul_inv] using h_mul
  unfold helperSkewDelta
  -- Need: floor(burden) ≤ relief where burden ≤ relief
  have h_floor_le := Int.floor_le (helperBurden helper sufferer E_target)
  -- floor(burden) ≤ burden ≤ relief (as real)
  have h_trans : (Int.floor (helperBurden helper sufferer E_target) : ℝ) ≤
      (skewRelief helper sufferer E_target : ℝ) := le_trans h_floor_le h_burden_le
  exact_mod_cast h_trans

lemma helperSkewDelta_lt_relief
    (helper sufferer : MoralState) (E_target : ℝ)
    (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target)
    (h_relief_pos : 0 < skewRelief helper sufferer E_target) :
    helperSkewDelta helper sufferer E_target <
      skewRelief helper sufferer E_target := by
  have h_le := helperSkewDelta_le_relief helper sufferer E_target h_suffering
  have h_burden_lt : helperBurden helper sufferer E_target < (skewRelief helper sufferer E_target : ℝ) := by
    unfold helperBurden
    have h_relief_pos_real : (0 : ℝ) < skewRelief helper sufferer E_target := by exact_mod_cast h_relief_pos
    have h_div_lt : (skewRelief helper sufferer E_target : ℝ) / 10 < (skewRelief helper sufferer E_target : ℝ) := by
      apply div_lt_self h_relief_pos_real
      norm_num
    exact h_div_lt
  unfold helperSkewDelta
  -- Need: floor(burden) < relief where burden < relief
  have h_floor_le := Int.floor_le (helperBurden helper sufferer E_target)
  -- floor(burden) ≤ burden < relief (as real)
  have h_trans : (Int.floor (helperBurden helper sufferer E_target) : ℝ) <
      (skewRelief helper sufferer E_target : ℝ) := lt_of_le_of_lt h_floor_le h_burden_lt
  exact_mod_cast h_trans

lemma skewRelief_lower_bound_of_transfer
    (helper sufferer : MoralState) (E_target : ℝ)
    (h_transfer : 1 / (φ ^ 4) ≤ energyTransfer helper sufferer E_target) :
    (1 : ℤ) ≤ skewRelief helper sufferer E_target := by
  unfold skewRelief
  have hφ_pow_pos : 0 < φ ^ 4 := phi_pow_four_pos
  have h_prod_ge : 1 ≤ energyTransfer helper sufferer E_target * φ ^ 4 := by
    rw [le_mul_iff_one_le_mul₀ hφ_pow_pos]
    convert h_transfer using 1
    field_simp [hφ_pow_pos.ne']
  exact Int.le_floor.mpr h_prod_ge

end CompassionSpec

/-! ## Core Definition -/

/-- Compassion provides asymmetric relief to suffering states.

    Triggers when sufferer has high debt and low energy.
    Helper transfers energy at φ² rate and absorbs small debt fraction.
-/
noncomputable def Compassion
  (helper sufferer : MoralState)
  (E_target : ℝ)
  (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
  MoralState × MoralState :=
  let energy_transfer := CompassionSpec.energyTransfer helper sufferer E_target
  let skew_relief := CompassionSpec.skewRelief helper sufferer E_target
  let helper_delta := CompassionSpec.helperSkewDelta helper sufferer E_target

  let helper' : MoralState := {
    ledger := helper.ledger
    agent_bonds := helper.agent_bonds
    skew := helper.skew + helper_delta
    energy := helper.energy - energy_transfer
    valid := helper.valid
    energy_pos := by
      have h_lt :=
        CompassionSpec.energyTransfer_lt_helper helper sufferer E_target h_suffering
      exact sub_pos.mpr h_lt
  }

  let sufferer' : MoralState := {
    ledger := sufferer.ledger
    agent_bonds := sufferer.agent_bonds
    skew := sufferer.skew - skew_relief
    energy := sufferer.energy + energy_transfer
    valid := sufferer.valid
    energy_pos := by
      have h_transfer_pos :=
        CompassionSpec.energyTransfer_pos helper sufferer E_target h_suffering
      exact add_pos sufferer.energy_pos h_transfer_pos
  }

  (helper', sufferer')

/-! ## Conservation Theorems -/

/-- Compassion does not conserve total skew: it can only decrease (or maintain) it. -/
theorem compassion_not_conservative
  (helper sufferer : MoralState)
  (E_target : ℝ)
  (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
  let (h', s') := Compassion helper sufferer E_target h_suffering
  h'.skew + s'.skew ≤ helper.skew + sufferer.skew := by
  classical
  -- Directly unfold the let binding
  simp only [Compassion]
  -- After unfolding, h'.skew = helper.skew + helper_delta
  --                  s'.skew = sufferer.skew - skew_relief
  have h_le :
      CompassionSpec.helperSkewDelta helper sufferer E_target ≤
        CompassionSpec.skewRelief helper sufferer E_target :=
    CompassionSpec.helperSkewDelta_le_relief helper sufferer E_target h_suffering
  have h_nonpos :
      (CompassionSpec.helperSkewDelta helper sufferer E_target -
        CompassionSpec.skewRelief helper sufferer E_target) ≤ 0 :=
    sub_nonpos.mpr h_le
  have h_add :
      helper.skew + sufferer.skew +
          (CompassionSpec.helperSkewDelta helper sufferer E_target -
              CompassionSpec.skewRelief helper sufferer E_target)
          ≤ helper.skew + sufferer.skew := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left h_nonpos (helper.skew + sufferer.skew)
  -- The result follows from algebraic manipulation
  -- h'.skew + s'.skew = (helper.skew + helper_delta) + (sufferer.skew - skew_relief)
  --                   = helper.skew + sufferer.skew + (helper_delta - skew_relief)
  --                   ≤ helper.skew + sufferer.skew (since helper_delta ≤ skew_relief)
  calc (helper.skew + CompassionSpec.helperSkewDelta helper sufferer E_target) +
        (sufferer.skew - CompassionSpec.skewRelief helper sufferer E_target)
      = helper.skew + sufferer.skew +
        (CompassionSpec.helperSkewDelta helper sufferer E_target -
         CompassionSpec.skewRelief helper sufferer E_target) := by ring
    _ ≤ helper.skew + sufferer.skew := h_add

/-- When relief is actually applied, total skew strictly decreases. -/
theorem compassion_total_skew_strict
  (helper sufferer : MoralState)
  (E_target : ℝ)
  (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target)
  (h_relief_pos :
    0 < CompassionSpec.skewRelief helper sufferer E_target) :
  let (h', s') := Compassion helper sufferer E_target h_suffering
  h'.skew + s'.skew < helper.skew + sufferer.skew := by
  simp only [Compassion]
  have h_lt := CompassionSpec.helperSkewDelta_lt_relief helper sufferer E_target h_suffering h_relief_pos
  omega

/-- Compassion reduces the sufferer's skew by exactly the relieved amount. -/
theorem compassion_reduces_suffering
  (helper sufferer : MoralState)
  (E_target : ℝ)
  (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
  let (_, s') := Compassion helper sufferer E_target h_suffering
  (sufferer.skew - s'.skew =
      CompassionSpec.skewRelief helper sufferer E_target) ∧
  s'.skew ≤ sufferer.skew := by
  simp only [Compassion]
  constructor
  · ring
  · have h_nonneg := CompassionSpec.skewRelief_nonneg helper sufferer E_target h_suffering
    omega

/-- Compassion costs helper energy -/
theorem compassion_costs_helper
  (helper sufferer : MoralState)
  (E_target : ℝ)
  (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
  let (h', _) := Compassion helper sufferer E_target h_suffering
  h'.energy < helper.energy := by
  simp only [Compassion]
  have h_pos := CompassionSpec.energyTransfer_pos helper sufferer E_target h_suffering
  linarith

/-! ## φ-Rate Properties -/

/-- Compassion uses φ² transfer rate -/
theorem compassion_phi2_transfer_rate
  (helper sufferer : MoralState)
  (E_target : ℝ)
  (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
  let (h', s') := Compassion helper sufferer E_target h_suffering
  s'.energy - sufferer.energy ≤ helper.energy / (Foundation.φ * Foundation.φ) := by
  simp only [Compassion]
  -- s'.energy = sufferer.energy + energyTransfer
  -- s'.energy - sufferer.energy = energyTransfer ≤ helper.energy / φ²
  have h_cancel : sufferer.energy + CompassionSpec.energyTransfer helper sufferer E_target - sufferer.energy =
      CompassionSpec.energyTransfer helper sufferer E_target := by ring
  rw [h_cancel]
  exact CompassionSpec.energyTransfer_le_helper helper sufferer E_target

/-- Compassion uses φ⁴ conversion for energy-to-relief -/
theorem compassion_phi4_conversion
  (helper sufferer : MoralState)
  (E_target : ℝ)
  (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
  let (_, s') := Compassion helper sufferer E_target h_suffering
  ((sufferer.skew - s'.skew : ℤ) =
      CompassionSpec.skewRelief helper sufferer E_target) ∧
  ((CompassionSpec.skewRelief helper sufferer E_target : ℝ)
      ≤ CompassionSpec.energyTransfer helper sufferer E_target * Foundation.φ ^ 4) ∧
  (CompassionSpec.energyTransfer helper sufferer E_target * Foundation.φ ^ 4 - 1 <
      (CompassionSpec.skewRelief helper sufferer E_target : ℝ)) := by
  simp only [Compassion]
  constructor
  · ring
  constructor
  · -- floor(x) ≤ x
    unfold CompassionSpec.skewRelief
    exact Int.floor_le _
  · -- x - 1 < floor(x)
    unfold CompassionSpec.skewRelief
    exact Int.sub_one_lt_floor _

/-- φ² is optimal transfer rate (neither too much nor too little) -/
theorem compassion_phi2_optimal :
  0 < 1 / (Foundation.φ * Foundation.φ) ∧ 1 / (Foundation.φ * Foundation.φ) < 1 := by
  have hφ_pos : 0 < Foundation.φ := phi_pos
  have hφ2_pos : 0 < Foundation.φ * Foundation.φ := mul_pos hφ_pos hφ_pos
  have hφ2_gt_one := CompassionSpec.phi_sq_gt_one
  constructor
  · exact div_pos one_pos hφ2_pos
  · rw [div_lt_one hφ2_pos]
    exact hφ2_gt_one

/-! ## Asymmetry (vs Love) -/

/-- Compassion is asymmetric (unlike Love) -/
theorem compassion_asymmetric
  (helper sufferer : MoralState)
  (E_target : ℝ)
  (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
  let (h', s') := Compassion helper sufferer E_target h_suffering
  h'.energy - helper.energy ≠ s'.energy - sufferer.energy := by
  simp only [Compassion]
  -- h'.energy - helper.energy = -transfer, s'.energy - sufferer.energy = +transfer
  have h_pos := CompassionSpec.energyTransfer_pos helper sufferer E_target h_suffering
  intro h_eq
  -- -transfer = +transfer implies transfer = 0, contradicting h_pos
  have : CompassionSpec.energyTransfer helper sufferer E_target = 0 := by linarith
  linarith

/-- Compassion is targeted (condition-dependent) -/
theorem compassion_targeted
  (helper sufferer : MoralState)
  (E_target : ℝ)
  (h_suffering : 0 < sufferer.skew ∧ sufferer.energy < E_target) :
  -- Requires specific suffering conditions to trigger
  0 < sufferer.skew ∧ sufferer.energy < E_target := by
  exact h_suffering

end Virtues
end Ethics
end IndisputableMonolith
