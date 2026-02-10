import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Physics.ElectronMass
import IndisputableMonolith.Physics.ElectronMass.Necessity
import IndisputableMonolith.Numerics.Interval.PhiBounds

/-!
# T14: The Neutrino Sector

This module formalizes the derivation of the neutrino mass scale.

## The Hypothesis

Neutrinos occupy the **Deep Ladder**: integer rungs far below the electron ($R_e = 2$).
Specifically, they appear to occupy even integers in the -50 range.

1.  **Mass 3 ($m_3$)**: The atmospheric scale corresponds to $R = -54$.
    $$ m_3 \approx m_{struct} \cdot \phi^{-54} \approx 0.056 \text{ eV} $$
    Observed (from $\Delta m^2_{32}$): $\approx 0.050$ eV.

2.  **Mass 2 ($m_2$)**: The solar scale corresponds to $R = -58$.
    $$ m_2 \approx m_{struct} \cdot \phi^{-58} \approx 0.0082 \text{ eV} $$
    Observed (from $\Delta m^2_{21}$): $\approx 0.0086$ eV.

## Interpretation

The residue difference between generations is $\Delta_{32} = 4$.
This suggests a spacing of 4 rungs, consistent with a quarter-ladder structure
where the "period" might be integers of 4.

-/

namespace IndisputableMonolith
namespace Physics
namespace NeutrinoSector

open Real Constants ElectronMass

/-! ## Experimental Values (PDG 2022) -/

/-- Mass squared differences (eV^2). -/
def dm2_21_exp : ℝ := 7.53e-5
def dm2_32_exp : ℝ := 2.453e-3

/-- Approximate masses assuming m1 ~ 0. -/
noncomputable def m2_approx : ℝ := Real.sqrt dm2_21_exp
noncomputable def m3_approx : ℝ := Real.sqrt dm2_32_exp

/-! ## The Deep Ladder -/

def rung_nu3 : ℤ := -54
def rung_nu2 : ℤ := -58

/-- Conversion from MeV (m_struct unit) to eV. -/
def MeV_to_eV : ℝ := 1e6

/-- Predicted Mass (eV). -/
noncomputable def predicted_mass_eV (rung : ℤ) : ℝ :=
  electron_structural_mass * (phi ^ rung) * MeV_to_eV

/-! ## Verification -/

/-- PROVEN: Bounds on the predicted m3 mass.

    Numerically: predicted_mass_eV (-54) ≈ 0.0563 eV
    m3_approx = sqrt(2.453e-3) ≈ 0.0495 eV
    |pred - exp| ≈ 0.0068 < 0.01

    Proof: Uses structural_mass ∈ (10856, 10858) and φ^(-54) ∈ (5.182e-12, 5.185e-12) -/
lemma nu3_pred_bounds : (0.055 : ℝ) < predicted_mass_eV rung_nu3 ∧ predicted_mass_eV rung_nu3 < (0.058 : ℝ) := by
  simp only [predicted_mass_eV, rung_nu3, MeV_to_eV]
  have h_sm := ElectronMass.Necessity.structural_mass_bounds
  have h_phi54_gt := IndisputableMonolith.Numerics.phi_neg54_gt
  have h_phi54_lt := IndisputableMonolith.Numerics.phi_neg54_lt
  have h_phi_eq : phi = Real.goldenRatio := rfl
  rw [h_phi_eq]
  have hpos_sm : (0 : ℝ) < electron_structural_mass := by
    have h := h_sm.1
    linarith
  have hpos_phi : (0 : ℝ) < Real.goldenRatio ^ (-54 : ℤ) := by
    have h := h_phi54_gt
    linarith
  constructor
  · -- 0.055 < structural_mass * φ^(-54) * 1e6
    -- Lower bound: 10856 * 5.182e-12 * 1e6 = 0.05626... > 0.055
    calc (0.055 : ℝ) < (10856 : ℝ) * (5.182e-12 : ℝ) * (1e6 : ℝ) := by norm_num
      _ < electron_structural_mass * (5.182e-12 : ℝ) * (1e6 : ℝ) := by nlinarith [h_sm.1]
      _ < electron_structural_mass * Real.goldenRatio ^ (-54 : ℤ) * (1e6 : ℝ) := by nlinarith [h_phi54_gt, hpos_sm]
  · -- structural_mass * φ^(-54) * 1e6 < 0.058
    -- Upper bound: 10858 * 5.185e-12 * 1e6 = 0.05629... < 0.058
    calc electron_structural_mass * Real.goldenRatio ^ (-54 : ℤ) * (1e6 : ℝ)
        < (10858 : ℝ) * Real.goldenRatio ^ (-54 : ℤ) * (1e6 : ℝ) := by nlinarith [h_sm.2, hpos_phi]
      _ < (10858 : ℝ) * (5.185e-12 : ℝ) * (1e6 : ℝ) := by nlinarith [h_phi54_lt]
      _ < (0.058 : ℝ) := by norm_num

/-- PROVEN: Bounds on m3_approx = sqrt(2.453e-3) ≈ 0.0495 eV
    Proof: 0.049² = 0.002401 < 0.002453 < 0.0025 = 0.050² -/
lemma m3_approx_bounds : (0.049 : ℝ) < m3_approx ∧ m3_approx < (0.050 : ℝ) := by
  simp only [m3_approx, dm2_32_exp]
  constructor
  · -- 0.049 < sqrt(0.002453)
    -- Equivalent to: 0.049² < 0.002453 (since both positive)
    have h1 : (0.049 : ℝ)^2 < 0.002453 := by norm_num
    have h_pos : (0 : ℝ) < 0.002453 := by norm_num
    have h_sqrt_pos : 0 < Real.sqrt 0.002453 := Real.sqrt_pos.mpr h_pos
    have h_049_pos : (0 : ℝ) ≤ 0.049 := by norm_num
    rw [← Real.sqrt_sq h_049_pos]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h1
  · -- sqrt(0.002453) < 0.050
    -- Equivalent to: 0.002453 < 0.050² (since both positive)
    have h1 : (0.002453 : ℝ) < 0.050^2 := by norm_num
    have h_pos : (0 : ℝ) ≤ 0.002453 := by norm_num
    have h_050_pos : (0 : ℝ) < 0.050 := by norm_num
    rw [← Real.sqrt_sq (le_of_lt h_050_pos)]
    exact Real.sqrt_lt_sqrt h_pos h1

/-- m3 matches the -54 rung to within tolerance (< 0.01 eV).

    Proof: From nu3_pred_bounds and m3_approx_bounds,
    |0.056 - 0.050| ≈ 0.006 < 0.01 ✓ -/
theorem nu3_match : abs (predicted_mass_eV rung_nu3 - m3_approx) < 0.01 := by
  have h_pred := nu3_pred_bounds
  have h_m3 := m3_approx_bounds
  -- pred ∈ (0.055, 0.058), m3 ∈ (0.049, 0.050)
  -- Worst case: |0.058 - 0.049| = 0.009 < 0.01 ✓
  rw [abs_lt]
  constructor <;> linarith [h_pred.1, h_pred.2, h_m3.1, h_m3.2]

/-- PROVEN: Bounds on the predicted m2 mass.

    Numerically: predicted_mass_eV (-58) ≈ 0.00821 eV
    m2_approx = sqrt(7.53e-5) ≈ 0.00868 eV
    |pred - exp| ≈ 0.00047 < 0.001

    Proof: Uses structural_mass ∈ (10856, 10858) and φ^(-58) ∈ (7.55e-13, 7.57e-13) -/
lemma nu2_pred_bounds : (0.0081 : ℝ) < predicted_mass_eV rung_nu2 ∧ predicted_mass_eV rung_nu2 < (0.0083 : ℝ) := by
  simp only [predicted_mass_eV, rung_nu2, MeV_to_eV]
  have h_sm := ElectronMass.Necessity.structural_mass_bounds
  have h_phi58_gt := IndisputableMonolith.Numerics.phi_neg58_gt
  have h_phi58_lt := IndisputableMonolith.Numerics.phi_neg58_lt
  have h_phi_eq : phi = Real.goldenRatio := rfl
  rw [h_phi_eq]
  have hpos_sm : (0 : ℝ) < electron_structural_mass := by
    have h := h_sm.1
    linarith
  have hpos_phi : (0 : ℝ) < Real.goldenRatio ^ (-58 : ℤ) := by
    have h := h_phi58_gt
    linarith
  constructor
  · -- 0.0081 < structural_mass * φ^(-58) * 1e6
    -- Lower bound: 10856 * 7.55e-13 * 1e6 = 0.00819... > 0.0081
    calc (0.0081 : ℝ) < (10856 : ℝ) * (7.55e-13 : ℝ) * (1e6 : ℝ) := by norm_num
      _ < electron_structural_mass * (7.55e-13 : ℝ) * (1e6 : ℝ) := by nlinarith [h_sm.1]
      _ < electron_structural_mass * Real.goldenRatio ^ (-58 : ℤ) * (1e6 : ℝ) := by nlinarith [h_phi58_gt, hpos_sm]
  · -- structural_mass * φ^(-58) * 1e6 < 0.0083
    -- Upper bound: 10858 * 7.57e-13 * 1e6 = 0.00821... < 0.0083
    calc electron_structural_mass * Real.goldenRatio ^ (-58 : ℤ) * (1e6 : ℝ)
        < (10858 : ℝ) * Real.goldenRatio ^ (-58 : ℤ) * (1e6 : ℝ) := by nlinarith [h_sm.2, hpos_phi]
      _ < (10858 : ℝ) * (7.57e-13 : ℝ) * (1e6 : ℝ) := by nlinarith [h_phi58_lt]
      _ < (0.0083 : ℝ) := by norm_num

/-- PROVEN: Bounds on m2_approx = sqrt(7.53e-5) ≈ 0.00868 eV
    Proof: 0.0086² = 7.396e-5 < 7.53e-5 < 7.744e-5 = 0.0088² -/
lemma m2_approx_bounds : (0.0086 : ℝ) < m2_approx ∧ m2_approx < (0.0088 : ℝ) := by
  simp only [m2_approx, dm2_21_exp]
  constructor
  · -- 0.0086 < sqrt(7.53e-5)
    have h1 : (0.0086 : ℝ)^2 < 7.53e-5 := by norm_num
    have h_pos : (0 : ℝ) < 7.53e-5 := by norm_num
    have h_sqrt_pos : 0 < Real.sqrt (7.53e-5) := Real.sqrt_pos.mpr h_pos
    have h_086_pos : (0 : ℝ) ≤ 0.0086 := by norm_num
    rw [← Real.sqrt_sq h_086_pos]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h1
  · -- sqrt(7.53e-5) < 0.0088
    have h1 : (7.53e-5 : ℝ) < 0.0088^2 := by norm_num
    have h_pos : (0 : ℝ) ≤ 7.53e-5 := by norm_num
    have h_088_pos : (0 : ℝ) < 0.0088 := by norm_num
    rw [← Real.sqrt_sq (le_of_lt h_088_pos)]
    exact Real.sqrt_lt_sqrt h_pos h1

/-- m2 matches the -58 rung to within tolerance (< 0.001 eV).

    Proof: From nu2_pred_bounds and m2_approx_bounds,
    |0.0082 - 0.0087| ≈ 0.0005 < 0.001 ✓ -/
theorem nu2_match : abs (predicted_mass_eV rung_nu2 - m2_approx) < 0.001 := by
  have h_pred := nu2_pred_bounds
  have h_m2 := m2_approx_bounds
  -- pred ∈ (0.0081, 0.0083), m2 ∈ (0.0086, 0.0088)
  -- Worst case: |0.0081 - 0.0088| = 0.0007 < 0.001 ✓
  rw [abs_lt]
  constructor <;> linarith [h_pred.1, h_pred.2, h_m2.1, h_m2.2]

/-- **CERTIFICATE: Neutrino Deep Ladder**
    Packages the proofs for atmospheric (m3) and solar (m2) neutrino mass matches. -/
structure NeutrinoMassCert where
  m3_match : abs (predicted_mass_eV rung_nu3 - m3_approx) < 0.01
  m2_match : abs (predicted_mass_eV rung_nu2 - m2_approx) < 0.001

theorem neutrino_mass_verified : NeutrinoMassCert where
  m3_match := nu3_match
  m2_match := nu2_match

end NeutrinoSector
end Physics
end IndisputableMonolith
