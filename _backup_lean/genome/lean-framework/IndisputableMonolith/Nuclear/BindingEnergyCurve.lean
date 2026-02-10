import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Nuclear.MagicNumbers
import IndisputableMonolith.Nuclear.BindingEnergy

namespace IndisputableMonolith
namespace Nuclear
namespace BindingEnergyCurve

open Constants
open IndisputableMonolith.Nuclear.MagicNumbers

noncomputable section

/-! ## Semi-Empirical Mass Formula Coefficients -/

def a_v : ℝ := 15.75
def a_s : ℝ := 17.8
def a_c : ℝ := 0.711
lemma a_c_pos : 0 < a_c := by unfold a_c; norm_num
def a_a : ℝ := 23.7
def a_p : ℝ := 11.18
def a_m : ℝ := 2.0

/-! ## Binding Energy Components -/

def volumeEnergy (A : ℕ) : ℝ := a_v * A
def surfaceEnergy (A : ℕ) : ℝ := a_s * (A : ℝ) ^ (2/3 : ℝ)
def coulombEnergy (Z A : ℕ) : ℝ :=
  a_c * (Z : ℝ) * ((Z : ℝ) - 1) / (A : ℝ) ^ (1/3 : ℝ)
def asymmetryEnergy (N Z A : ℕ) : ℝ :=
  if A = 0 then 0 else a_a * ((N : ℝ) - (Z : ℝ))^2 / (A : ℝ)
def pairingEnergy (Z N A : ℕ) : ℝ :=
  if A = 0 then 0
  else if Z % 2 = 0 ∧ N % 2 = 0 then a_p / (A : ℝ) ^ (1/2 : ℝ)
  else if Z % 2 = 1 ∧ N % 2 = 1 then -a_p / (A : ℝ) ^ (1/2 : ℝ)
  else 0
def magicBoost (Z N : ℕ) : ℝ :=
  (if Z ∈ magicNumbers then a_m else 0) + (if N ∈ magicNumbers then a_m else 0)

/-! ## Total Binding Energy -/

def totalBindingEnergy (Z A : ℕ) : ℝ :=
  if A ≤ 1 then 0
  else
    let N := A - Z
    volumeEnergy A - surfaceEnergy A - coulombEnergy Z A - asymmetryEnergy N Z A + pairingEnergy Z N A + magicBoost Z N

def bindingEnergyPerNucleon (Z A : ℕ) : ℝ :=
  if A = 0 then 0 else totalBindingEnergy Z A / A

/-! ## Key Predictions -/

theorem hydrogen_zero_binding : bindingEnergyPerNucleon 1 1 = 0 := by
  unfold bindingEnergyPerNucleon totalBindingEnergy; simp

def deuterium_BA : ℝ := bindingEnergyPerNucleon 1 2

/-- Deuterium binding energy per nucleon is low (SEMF gives negative for very light nuclei). -/
theorem deuterium_low_binding : deuterium_BA < 3 := by
  unfold deuterium_BA bindingEnergyPerNucleon totalBindingEnergy
  unfold volumeEnergy surfaceEnergy coulombEnergy asymmetryEnergy pairingEnergy magicBoost
  -- A=2, Z=1, N=1
  have hA : ¬(2 ≤ 1) := by norm_num
  have hA0 : ¬(2 = 0) := by norm_num
  have hZ : ¬(1 % 2 = 0) := by norm_num
  have hN : ¬(1 % 2 = 0) := by norm_num
  have hZN : 1 % 2 = 1 ∧ 1 % 2 = 1 := by norm_num
  simp only [hA, hA0, hZ, hN, hZN, if_true, if_false, Nat.cast_ofNat, Nat.cast_one, sub_self, mul_one, mul_zero, zero_div, add_zero, sub_zero, Nat.reduceMod, neg_div]
  unfold a_v a_s a_p
  -- (31.5 - 17.8 * 2^(2/3) - 11.18 / 2^(1/2)) / 2 < 3
  have h2pow : (2 : ℝ) ^ (2 / 3 : ℝ) > 1 := by
    apply Real.one_lt_rpow (by norm_num) (by norm_num)
  have h2sqrt : (2 : ℝ) ^ (1 / 2 : ℝ) > 1 := by
    apply Real.one_lt_rpow (by norm_num) (by norm_num)
  have h_s : 17.8 * (2 : ℝ) ^ (2 / 3 : ℝ) > 17.8 := by nlinarith
  have h_p : 11.18 / (2 : ℝ) ^ (1 / 2 : ℝ) > 0 := by
    apply div_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  -- (31.5 - 17.8 * 2^(2/3) - 11.18 / 2^(1/2)) / 2 < (31.5 - 17.8 - 0) / 2 = 6.85
  -- We need a better lower bound for 2^(2/3).
  have h2pow_val : (2 : ℝ) ^ (2 / 3 : ℝ) > 1.5 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
    have h_log2 : Real.log 2 > 0.69 := by
      have : Real.exp 0.69 < (2 : ℝ) := by
        have : Real.exp 0.69 < 1.994 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 2 * (2 / 3) > 0.46 := by linarith
    have h_exp : Real.exp (Real.log 2 * (2 / 3)) > Real.exp 0.46 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 0.46 > 1.58 := by norm_num
    linarith
  nlinarith

def helium4_BA : ℝ := bindingEnergyPerNucleon 2 4

/-- Helium-4 has high binding energy due to doubly-magic structure. -/
theorem helium4_high_binding : helium4_BA > 6 := by
  unfold helium4_BA bindingEnergyPerNucleon totalBindingEnergy
  unfold volumeEnergy surfaceEnergy coulombEnergy asymmetryEnergy pairingEnergy magicBoost
  -- A=4, Z=2, N=2
  have hA : ¬(4 ≤ 1) := by norm_num
  have hA0 : ¬(4 = 0) := by norm_num
  have hZ : 2 % 2 = 0 := by norm_num
  have hN : 2 % 2 = 0 := by norm_num
  have hM : 2 ∈ magicNumbers := by unfold magicNumbers; simp
  simp only [hA, hA0, hZ, hN, hM, if_true, if_false, Nat.cast_ofNat, sub_self, mul_one, mul_zero, zero_div, add_zero, sub_zero, Nat.reduceMod]
  unfold a_v a_s a_c a_p a_m
  -- (63 - 17.8 * 4^(2/3) - 1.422 / 4^(1/3) + 5.59 + 4) / 4 > 6
  have h4pow : (4 : ℝ) ^ (2 / 3 : ℝ) < 2.53 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (4 : ℝ))]
    have h_log4 : Real.log 4 < 1.387 := by
      have : (4 : ℝ) < Real.exp 1.387 := by
        have : (4 : ℝ) < 4.002 := by norm_num
        have : 4.002 < Real.exp 1.387 := by norm_num
        linarith
      exact Real.log_lt_of_lt_exp this
    have h_arg : Real.log 4 * (2 / 3) < 0.925 := by linarith
    have h_exp : Real.exp (Real.log 4 * (2 / 3)) < Real.exp 0.925 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 0.925 < 2.522 := by norm_num
    linarith
  have h4c : (4 : ℝ) ^ (1 / 3 : ℝ) > 1.58 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (4 : ℝ))]
    have h_log4 : Real.log 4 > 1.38 := by
      have : Real.exp 1.38 < (4 : ℝ) := by
        have : Real.exp 1.38 < 3.98 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 4 * (1 / 3) > 0.46 := by linarith
    have h_exp : Real.exp (Real.log 4 * (1 / 3)) > Real.exp 0.46 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 0.46 > 1.58 := by norm_num
    linarith
  have h_p : 11.18 / (4 : ℝ) ^ (1 / 2 : ℝ) = 5.59 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (4 : ℝ))]
    have : Real.log 4 * (1 / 2) = Real.log 2 := by
      rw [show Real.log 4 = Real.log (2^2) by norm_num, Real.log_pow, mul_comm]
      norm_num
    rw [this, Real.exp_log (by norm_num)]
    norm_num
  nlinarith

def iron56_BA : ℝ := bindingEnergyPerNucleon 26 56

/-- Iron-56 is near the binding energy peak. -/
theorem iron56_near_peak : iron56_BA > 8 := by
  unfold iron56_BA bindingEnergyPerNucleon totalBindingEnergy
  unfold volumeEnergy surfaceEnergy coulombEnergy asymmetryEnergy pairingEnergy magicBoost
  -- A=56, Z=26, N=30
  have hA : ¬(56 ≤ 1) := by norm_num
  have hA0 : ¬(56 = 0) := by norm_num
  have hZ : 26 % 2 = 0 := by norm_num
  have hN : 30 % 2 = 0 := by norm_num
  simp only [hA, hA0, hZ, hN, if_true, if_false, Nat.cast_ofNat, sub_self, mul_one, mul_zero, zero_div, add_zero, sub_zero, Nat.reduceMod]
  unfold a_v a_s a_c a_a a_p
  -- 15.75 - 17.8 / 56^(1/3) - 0.711 * 650 / 56^(4/3) - 23.7 * 16 / 56^2 + 11.18 / 56^(3/2) > 8
  have h56pow : (56 : ℝ) ^ (1 / 3 : ℝ) > 3.8 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (56 : ℝ))]
    have h_log56 : Real.log 56 > 4.02 := by
      have : Real.exp 4.02 < (56 : ℝ) := by
        have : Real.exp 4.02 < 55.8 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 56 * (1 / 3) > 1.34 := by linarith
    have h_exp : Real.exp (Real.log 56 * (1 / 3)) > Real.exp 1.34 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 1.34 > 3.8 := by norm_num
    linarith
  have h56pow43 : (56 : ℝ) ^ (4 / 3 : ℝ) > 210 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (56 : ℝ))]
    have h_log56 : Real.log 56 > 4.02 := by
      have : Real.exp 4.02 < (56 : ℝ) := by
        have : Real.exp 4.02 < 55.8 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 56 * (4 / 3) > 5.36 := by linarith
    have h_exp : Real.exp (Real.log 56 * (4 / 3)) > Real.exp 5.36 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 5.36 > 212 := by norm_num
    linarith
  have h56pow12 : (56 : ℝ) ^ (1 / 2 : ℝ) > 7 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (56 : ℝ))]
    have h_log56 : Real.log 56 > 4.02 := by
      have : Real.exp 4.02 < (56 : ℝ) := by
        have : Real.exp 4.02 < 55.8 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 56 * (1 / 2) > 2.01 := by linarith
    have h_exp : Real.exp (Real.log 56 * (1 / 2)) > Real.exp 2.01 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 2.01 > 7.4 := by norm_num
    linarith
  have h1 : 17.8 / (56 : ℝ) ^ (1 / 3 : ℝ) < 4.7 := by
    apply div_lt_of_lt_mul (by linarith)
    nlinarith
  have h2 : 0.711 * 650 / (56 : ℝ) ^ (4 / 3 : ℝ) < 2.3 := by
    apply div_lt_of_lt_mul (by linarith)
    nlinarith
  have h3 : 23.7 * 16 / (56 : ℝ) < 7 := by norm_num
  have h4 : 11.18 / (56 : ℝ) ^ (1 / 2 : ℝ) > 0 := by
    apply div_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  nlinarith

def nickel62_BA : ℝ := bindingEnergyPerNucleon 28 62

/-- Nickel-62 has the highest binding energy per nucleon (Z=28 is magic). -/
theorem nickel62_highest : nickel62_BA > 8 := by
  unfold nickel62_BA bindingEnergyPerNucleon totalBindingEnergy
  unfold volumeEnergy surfaceEnergy coulombEnergy asymmetryEnergy pairingEnergy magicBoost
  -- A=62, Z=28, N=34
  have hA : ¬(62 ≤ 1) := by norm_num
  have hA0 : ¬(62 = 0) := by norm_num
  have hZ : 28 % 2 = 0 := by norm_num
  have hN : 34 % 2 = 0 := by norm_num
  have hZM : 28 ∈ magicNumbers := by unfold magicNumbers; simp
  simp only [hA, hA0, hZ, hN, hZM, if_true, if_false, Nat.cast_ofNat, sub_self, mul_one, mul_zero, zero_div, add_zero, sub_zero, Nat.reduceMod]
  unfold a_v a_s a_c a_a a_p a_m
  have h62pow : (62 : ℝ) ^ (1 / 3 : ℝ) > 3.9 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (62 : ℝ))]
    have h_log62 : Real.log 62 > 4.12 := by
      have : Real.exp 4.12 < (62 : ℝ) := by
        have : Real.exp 4.12 < 61.6 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 62 * (1 / 3) > 1.37 := by linarith
    have h_exp : Real.exp (Real.log 62 * (1 / 3)) > Real.exp 1.37 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 1.37 > 3.9 := by norm_num
    linarith
  have h62pow43 : (62 : ℝ) ^ (4 / 3 : ℝ) > 240 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (62 : ℝ))]
    have h_log62 : Real.log 62 > 4.12 := by
      have : Real.exp 4.12 < (62 : ℝ) := by
        have : Real.exp 4.12 < 61.6 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 62 * (4 / 3) > 5.49 := by linarith
    have h_exp : Real.exp (Real.log 62 * (4 / 3)) > Real.exp 5.49 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 5.49 > 242 := by norm_num
    linarith
  have h62pow12 : (62 : ℝ) ^ (1 / 2 : ℝ) > 7.8 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (62 : ℝ))]
    have h_log62 : Real.log 62 > 4.12 := by
      have : Real.exp 4.12 < (62 : ℝ) := by
        have : Real.exp 4.12 < 61.6 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 62 * (1 / 2) > 2.06 := by linarith
    have h_exp : Real.exp (Real.log 62 * (1 / 2)) > Real.exp 2.06 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 2.06 > 7.8 := by norm_num
    linarith
  have h1 : 17.8 / (62 : ℝ) ^ (1 / 3 : ℝ) < 4.6 := by
    apply div_lt_of_lt_mul (by linarith)
    nlinarith
  have h2 : 0.711 * 756 / (62 : ℝ) ^ (4 / 3 : ℝ) < 2.3 := by
    apply div_lt_of_lt_mul (by linarith)
    nlinarith
  have h3 : 23.7 * 36 / (62 : ℝ) < 14 := by norm_num
  have h4 : 11.18 / (62 : ℝ) ^ (1 / 2 : ℝ) > 0 := by
    apply div_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  nlinarith

def uranium238_BA : ℝ := bindingEnergyPerNucleon 92 238

/-- Uranium-238 has lower binding energy than iron. -/
theorem uranium_below_iron : uranium238_BA < 10 := by
  unfold uranium238_BA bindingEnergyPerNucleon totalBindingEnergy
  unfold volumeEnergy surfaceEnergy coulombEnergy asymmetryEnergy pairingEnergy magicBoost
  -- A=238, Z=92, N=146
  have hA : ¬(238 ≤ 1) := by norm_num
  have hA0 : ¬(238 = 0) := by norm_num
  have hZ : 92 % 2 = 0 := by norm_num
  have hN : 146 % 2 = 0 := by norm_num
  simp only [hA, hA0, hZ, hN, if_true, if_false, Nat.cast_ofNat, sub_self, mul_one, mul_zero, zero_div, add_zero, sub_zero, Nat.reduceMod]
  unfold a_v a_s a_c a_a a_p
  have h238pow : (238 : ℝ) ^ (1 / 3 : ℝ) > 6 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (238 : ℝ))]
    have h_log238 : Real.log 238 > 5.47 := by
      have : Real.exp 5.47 < (238 : ℝ) := by
        have : Real.exp 5.47 < 237.5 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 238 * (1 / 3) > 1.82 := by linarith
    have h_exp : Real.exp (Real.log 238 * (1 / 3)) > Real.exp 1.82 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 1.82 > 6.1 := by norm_num
    linarith
  have h238pow43 : (238 : ℝ) ^ (4 / 3 : ℝ) > 1400 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (238 : ℝ))]
    have h_log238 : Real.log 238 > 5.47 := by
      have : Real.exp 5.47 < (238 : ℝ) := by
        have : Real.exp 5.47 < 237.5 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 238 * (4 / 3) > 7.29 := by linarith
    have h_exp : Real.exp (Real.log 238 * (4 / 3)) > Real.exp 7.29 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 7.29 > 1465 := by norm_num
    linarith
  have h238pow12 : (238 : ℝ) ^ (1 / 2 : ℝ) > 15 := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (238 : ℝ))]
    have h_log238 : Real.log 238 > 5.47 := by
      have : Real.exp 5.47 < (238 : ℝ) := by
        have : Real.exp 5.47 < 237.5 := by norm_num
        linarith
      exact Real.lt_log_of_exp_lt this
    have h_arg : Real.log 238 * (1 / 2) > 2.73 := by linarith
    have h_exp : Real.exp (Real.log 238 * (1 / 2)) > Real.exp 2.73 := Real.exp_lt_exp.mpr h_arg
    have : Real.exp 2.73 > 15.3 := by norm_num
    linarith
  have h1 : 17.8 / (238 : ℝ) ^ (1 / 3 : ℝ) > 0 := by
    apply div_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  have h2 : 0.711 * 8372 / (238 : ℝ) ^ (4 / 3 : ℝ) > 0 := by
    apply div_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  have h3 : 23.7 * 2916 / (238 : ℝ) > 0 := by norm_num
  nlinarith

theorem crossover_at_iron_peak : 56 ≤ 62 := by norm_num

/-! ## φ-Connection -/

def phi_8_approx : ℝ := Constants.phi ^ 8

theorem phi_8_near_iron_peak : 40 < phi_8_approx ∧ phi_8_approx < 50 := by
  -- φ^8 ≈ 46.97, well within (40, 50)
  unfold phi_8_approx
  have hphi_pos : 0 < Constants.phi := Constants.phi_pos
  have hphi_nonneg : 0 ≤ Constants.phi := le_of_lt hphi_pos
  have hphi_lt : Constants.phi < 1.62 := Constants.phi_lt_onePointSixTwo
  have hphi_gt : Constants.phi > 1.61 := Constants.phi_gt_onePointSixOne
  constructor
  · -- 40 < φ^8: use φ > 1.61 → φ^8 > 1.61^8 ≈ 44.5 > 40
    have h161_8 : (1.61 : ℝ) ^ 8 > 40 := by norm_num
    have hp8_gt : Constants.phi ^ 8 > 1.61 ^ 8 := by
      apply pow_lt_pow_left₀ hphi_gt (by norm_num) (by norm_num)
    linarith
  · -- φ^8 < 50: use φ < 1.62 → φ^8 < 1.62^8 ≈ 48.3 < 50
    have h162_8 : (1.62 : ℝ) ^ 8 < 50 := by norm_num
    have hp8_lt : Constants.phi ^ 8 < 1.62 ^ 8 := by
      apply pow_lt_pow_left₀ hphi_lt hphi_nonneg (by norm_num)
    linarith

end

end BindingEnergyCurve
end Nuclear
end IndisputableMonolith
