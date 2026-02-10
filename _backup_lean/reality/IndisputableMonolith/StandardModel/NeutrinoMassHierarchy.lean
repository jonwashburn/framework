import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Numerics.Interval.PhiBounds

namespace IndisputableMonolith
namespace StandardModel
namespace NeutrinoMassHierarchy

open Real
open IndisputableMonolith.Constants
open IndisputableMonolith.Numerics

/-! ## Observed Mass Differences -/

noncomputable def deltam21_sq : ℝ := 7.42e-5
noncomputable def deltam31_sq : ℝ := 2.51e-3
noncomputable def sum_mass_bound : ℝ := 0.12

/-! ## The Seesaw Mechanism -/

noncomputable def seesawMass (mD MR : ℝ) : ℝ := mD^2 / MR
noncomputable def typicalDiracMass : ℝ := 100
noncomputable def typicalMajoranaMass : ℝ := 1e14

theorem seesaw_gives_small_mass :
    seesawMass typicalDiracMass typicalMajoranaMass = 1e-10 := by
  unfold seesawMass typicalDiracMass typicalMajoranaMass
  norm_num

/-! ## φ-Connection to the Seesaw Scale -/

noncomputable def phiPredictedMR : ℝ := (1.2e19) / phi^13

/-- Auxiliary lemma for phi^13 using Fibonacci numbers. -/
lemma phi_pow13 : phi^13 = 233 * phi + 144 := by
  have h2 : phi^2 = phi + 1 := phi_sq_eq
  have h3 : phi^3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi^4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  have h5 : phi^5 = 5 * phi + 3 := by rw [pow_succ, h4]; ring_nf; rw [h2]; ring_nf
  have h6 : phi^6 = 8 * phi + 5 := by rw [pow_succ, h5]; ring_nf; rw [h2]; ring_nf
  have h7 : phi^7 = 13 * phi + 8 := by rw [pow_succ, h6]; ring_nf; rw [h2]; ring_nf
  have h8 : phi^8 = 21 * phi + 13 := by rw [pow_succ, h7]; ring_nf; rw [h2]; ring_nf
  have h9 : phi^9 = 34 * phi + 21 := by rw [pow_succ, h8]; ring_nf; rw [h2]; ring_nf
  have h10 : phi^10 = 55 * phi + 34 := by rw [pow_succ, h9]; ring_nf; rw [h2]; ring_nf
  have h11 : phi^11 = 89 * phi + 55 := by rw [pow_succ, h10]; ring_nf; rw [h2]; ring_nf
  have h12 : phi^12 = 144 * phi + 89 := by rw [pow_succ, h11]; ring_nf; rw [h2]; ring_nf
  have h13 : phi^13 = 233 * phi + 144 := by rw [pow_succ, h12]; ring_nf; rw [h2]; ring_nf
  exact h13

theorem seesaw_scale_phi_connection :
    abs (phiPredictedMR - (2.3e16 : ℝ)) < (1e15 : ℝ) := by
  unfold phiPredictedMR
  -- phi = goldenRatio
  have h_phi_eq : phi = goldenRatio := rfl
  have hlo : (1.618 : ℝ) < phi := by rw [h_phi_eq]; exact phi_gt_1618
  have hhi : phi < (1.6185 : ℝ) := by rw [h_phi_eq]; exact phi_lt_16185
  have h13lo : (520 : ℝ) < phi^13 := by
    rw [phi_pow13]
    have : (520 : ℝ) < 233 * (1.618 : ℝ) + 144 := by norm_num
    linarith
  have h13hi : phi^13 < (522 : ℝ) := by
    rw [phi_pow13]
    have : 233 * (1.6185 : ℝ) + 144 < (522 : ℝ) := by norm_num
    linarith
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt]
    apply (lt_div_iff₀ (pow_pos phi_pos 13)).mpr
    have : (2.3e16 - 1e15 : ℝ) * 522 < 1.2e19 := by norm_num
    linarith
  · rw [sub_lt_iff_lt_add]
    apply (div_lt_iff₀ (pow_pos phi_pos 13)).mpr
    have : (2.3e16 + 1e15 : ℝ) * 520 > 1.2e19 := by norm_num
    linarith

/-! ## Mass Hierarchy -/

noncomputable def massRatio : ℝ := deltam31_sq / deltam21_sq

lemma phi_pow7 : phi^7 = 13 * phi + 8 := by
  have h2 : phi^2 = phi + 1 := phi_sq_eq
  have h3 : phi^3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi^4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  have h5 : phi^5 = 5 * phi + 3 := by rw [pow_succ, h4]; ring_nf; rw [h2]; ring_nf
  have h6 : phi^6 = 8 * phi + 5 := by rw [pow_succ, h5]; ring_nf; rw [h2]; ring_nf
  have h7 : phi^7 = 13 * phi + 8 := by rw [pow_succ, h6]; ring_nf; rw [h2]; ring_nf
  exact h7

theorem mass_ratio_phi7 :
    abs (massRatio - (phi^7 * (1.17 : ℝ))) < (0.5 : ℝ) := by
  unfold massRatio deltam31_sq deltam21_sq
  -- phi = goldenRatio
  have h_phi_eq : phi = goldenRatio := rfl
  have hlo : (1.618 : ℝ) < phi := by rw [h_phi_eq]; exact phi_gt_1618
  have hhi : phi < (1.6185 : ℝ) := by rw [h_phi_eq]; exact phi_lt_16185
  have hRatio_lo : (33.8 : ℝ) < (2.51e-3 / 7.42e-5 : ℝ) := by norm_num
  have hRatio_hi : (2.51e-3 / 7.42e-5 : ℝ) < (33.9 : ℝ) := by norm_num
  have hPhi7_lo : (33.9 : ℝ) < phi^7 * 1.17 := by
    rw [phi_pow7]
    have : (33.9 : ℝ) < (13 * (1.618 : ℝ) + 8) * 1.17 := by norm_num
    nlinarith
  have hPhi7_hi : phi^7 * 1.17 < (34.1 : ℝ) := by
    rw [phi_pow7]
    have : (13 * (1.6185 : ℝ) + 8) * 1.17 < 34.1 := by norm_num
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-! ## Individual Masses from φ -/

noncomputable def m2_estimate : ℝ := sqrt deltam21_sq * 1000
noncomputable def m3_estimate : ℝ := sqrt deltam31_sq * 1000
noncomputable def m3_m2_ratio : ℝ := m3_estimate / m2_estimate

lemma phi_pow4 : phi^4 = 3 * phi + 2 := by
  have h2 : phi^2 = phi + 1 := phi_sq_eq
  have h3 : phi^3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi^4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  exact h4

theorem mass_ratio_phi4 :
    abs (m3_m2_ratio / phi^4 - 1) < (0.2 : ℝ) := by
  unfold m3_m2_ratio m3_estimate m2_estimate deltam31_sq deltam21_sq
  -- phi = goldenRatio
  have h_phi_eq : phi = goldenRatio := rfl
  have hlo : (1.618 : ℝ) < phi := by rw [h_phi_eq]; exact phi_gt_1618
  have hhi : phi < (1.6185 : ℝ) := by rw [h_phi_eq]; exact phi_lt_16185
  have h_num : (0 : ℝ) ≤ 2.51e-3 := by norm_num
  have h_den : (0 : ℝ) ≤ 7.42e-5 := by norm_num
  have h_val : sqrt 2.51e-3 / sqrt 7.42e-5 = sqrt (2.51e-3 / 7.42e-5) := by
    rw [sqrt_div h_num]
  have hRatio_lo : (5.8 : ℝ) < sqrt (2.51e-3 / 7.42e-5) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hRatio_hi : sqrt (2.51e-3 / 7.42e-5) < (5.9 : ℝ) := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, mul_div_mul_right _ _ (by norm_num : (1000 : ℝ) ≠ 0), h_val]
    apply (lt_div_iff₀ (pow_pos phi_pos 4)).mpr
    have h4hi : phi^4 < (6.9 : ℝ) := by
      rw [phi_pow4]
      have : 3 * (1.6185 : ℝ) + 2 < 6.9 := by norm_num
      linarith
    have : (0.8 : ℝ) * 6.9 < 5.8 := by norm_num
    linarith
  · rw [sub_lt_iff_lt_add, mul_div_mul_right _ _ (by norm_num : (1000 : ℝ) ≠ 0), h_val]
    apply (div_lt_iff₀ (pow_pos phi_pos 4)).mpr
    have h4lo : phi^4 > (6.8 : ℝ) := by
      rw [phi_pow4]
      have : 3 * (1.618 : ℝ) + 2 > 6.8 := by norm_num
      linarith
    have : 5.9 < (1.2 : ℝ) * 6.8 := by norm_num
    linarith

inductive MassOrdering
| Normal
| Inverted
deriving Repr, DecidableEq

def rsPrediction : MassOrdering := MassOrdering.Normal
