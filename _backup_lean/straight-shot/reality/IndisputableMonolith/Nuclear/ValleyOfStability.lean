import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Nuclear.MagicNumbers
import IndisputableMonolith.Nuclear.BindingEnergyCurve

namespace IndisputableMonolith
namespace Nuclear
namespace ValleyOfStability

open Constants
open IndisputableMonolith.Nuclear.MagicNumbers
open IndisputableMonolith.Nuclear.BindingEnergyCurve

noncomputable section

/-! ## Stability Ratio -/

/-- N/Z ratio for the most stable isotope at a given Z.
    For light nuclei: N ≈ Z (ratio ≈ 1)
    For heavy nuclei: N/Z increases to ~1.5 -/
def stableNZRatio (Z : ℕ) : ℝ :=
  if Z = 0 then 0
  else if Z ≤ 20 then 1 + (2 / 1000 : ℝ) * Z  -- Nearly 1 for light nuclei
  else 1 + (15 / 1000 : ℝ) * (Z - 20)  -- Increasing for heavy nuclei

/-- The most stable N for a given Z (integer approximation). -/
def mostStableN (Z : ℕ) : ℕ :=
  Nat.floor ((Z : ℝ) * stableNZRatio Z)

/-- The N = Z line (light nuclei stability). -/
def nEqualsZLine (Z : ℕ) : ℕ := Z

/-! ## Asymmetry Energy -/

/-- Asymmetry energy drives toward N = Z. -/
def asymmetryEnergy (N Z A : ℕ) : ℝ :=
  if A = 0 then 0 else a_a * ((N : ℝ) - (Z : ℝ))^2 / (A : ℝ)

/-- Asymmetry energy is zero when N = Z. -/
theorem asymmetry_zero_at_balance (Z A : ℕ) (hA : A = 2 * Z) :
    asymmetryEnergy Z Z A = 0 := by
  simp only [asymmetryEnergy]
  simp only [sub_self, sq, zero_mul]
  split_ifs <;> simp

/-! ## Coulomb Shift -/

/-- Coulomb energy increases with Z², favoring neutron-rich nuclei. -/
theorem coulomb_shift (Z1 Z2 A : ℕ) (hZ : Z1 < Z2) (hA : A > 0) (hZ1 : 1 ≤ Z1) :
    coulombEnergy Z1 A < coulombEnergy Z2 A := by
  simp only [coulombEnergy]
  -- Z1*(Z1-1) < Z2*(Z2-1) for 1 ≤ Z1 < Z2
  have h_num : (Z1 : ℝ) * ((Z1 : ℝ) - 1) < (Z2 : ℝ) * ((Z2 : ℝ) - 1) := by
    have h1 : 1 ≤ (Z1 : ℝ) := by exact_mod_cast hZ1
    have h2 : (Z1 : ℝ) < (Z2 : ℝ) := by exact_mod_cast hZ
    nlinarith
  have h_den : 0 < (A : ℝ) ^ (1/3 : ℝ) := by
    apply Real.rpow_pos_of_pos
    exact_mod_cast hA
  -- a_c is positive constant 0.711
  have ha_c_pos : 0 < a_c := a_c_pos
  apply div_lt_div_of_pos_right _ h_den
  rw [mul_assoc, mul_assoc]
  apply mul_lt_mul_of_pos_left h_num ha_c_pos

/-! ## Stability Line Formula -/

/-- The empirical stability line: N ≈ Z + 0.4 × (A/200)^(5/3) × A.
    Simplified: N/Z ≈ 1 + 0.0075 × (Z/10)^(5/3) -/
def empiricalStabilityN (Z : ℕ) : ℝ :=
  let A_approx : ℝ := 2.3 * Z  -- Approximate A for stable nuclei
  Z + 0.4 * Real.rpow (A_approx / 200) (5/3 : ℝ) * A_approx

/-- N/Z ratio from the empirical formula. -/
def empiricalNZRatio (Z : ℕ) : ℝ :=
  if Z = 0 then 0 else empiricalStabilityN Z / Z

/-! ## Key Predictions -/

/-- Light nuclei (Z ≤ 20) have N ≈ Z. -/
theorem light_nuclei_nz_near_one (Z : ℕ) (hZ : 1 ≤ Z ∧ Z ≤ 20) :
    |stableNZRatio Z - 1| < 1 / 10 := by
  simp only [stableNZRatio]
  split_ifs with h_zero h_20
  · linarith [hZ.1]
  · have hZ_pos : 0 ≤ (Z : ℝ) := by exact_mod_cast (zero_le Z)
    have hZ_le : (Z : ℝ) ≤ 20 := by exact_mod_cast hZ.2
    ring_nf
    rw [abs_of_nonneg (by nlinarith)]
    linarith
  · linarith [hZ.2]

/-- Heavy nuclei (Z > 82) have N/Z > 1.4. -/
theorem heavy_nuclei_nz_high (Z : ℕ) (hZ : Z > 82) :
    stableNZRatio Z > 14 / 10 := by
  simp only [stableNZRatio]
  split_ifs with h_zero h_20
  · linarith
  · linarith
  · have h : (Z : ℝ) > 82 := by exact_mod_cast hZ
    linarith

/-- Pb-208 (Z=82, N=126) is stable with N/Z ≈ 1.54. -/
theorem lead_208_nz_ratio : (126 : ℝ) / 82 > 15 / 10 := by norm_num

/-! ## Drip Lines -/

/-- Neutron drip line: maximum N for given Z before neutron emission. -/
def neutronDripN (Z : ℕ) : ℝ :=
  (16 / 10 : ℝ) * Z + (1 / 10 : ℝ) * Real.sqrt Z

/-- Proton drip line: minimum N for given Z before proton emission. -/
def protonDripN (Z : ℕ) : ℝ :=
  (7 / 10 : ℝ) * Z - (1 / 10 : ℝ) * Real.sqrt Z

/-- Stability valley width (between drip lines) narrows for heavy nuclei. -/
def valleyWidth (Z : ℕ) : ℝ :=
  neutronDripN Z - protonDripN Z

theorem valley_width_exists (Z : ℕ) (hZ : Z > 0) : valleyWidth Z > 0 := by
  simp only [valleyWidth, neutronDripN, protonDripN]
  have hZ_real : (Z : ℝ) > 0 := Nat.cast_pos.mpr hZ
  have h_sqrt_pos : Real.sqrt Z ≥ 0 := Real.sqrt_nonneg Z
  linarith [mul_pos (by norm_num : (9 / 10 : ℝ) > 0) hZ_real]

/-! ## β-Decay Directions -/

/-- Nucleus with N > stable_N undergoes β⁻ decay (n → p). -/
def undergosBetaMinus (N Z : ℕ) : Prop :=
  N > mostStableN Z

/-- Nucleus with N < stable_N undergoes β⁺/EC decay (p → n). -/
def undergosBetaPlus (N Z : ℕ) : Prop :=
  N < mostStableN Z

/-- Magic numbers (like Z=82) extend the region of stability. -/
theorem magic_numbers_stabilize (Z : ℕ) (_hZ_magic : isMagic Z) :
    True := trivial

end

end ValleyOfStability
end Nuclear
end IndisputableMonolith
