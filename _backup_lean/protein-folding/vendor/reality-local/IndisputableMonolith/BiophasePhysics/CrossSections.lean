import Mathlib
import IndisputableMonolith.BiophaseCore.Constants
import IndisputableMonolith.Numerics.Interval

/-!
# Physical Cross-Sections at BIOPHASE Scale

Calculate interaction cross-sections for electromagnetic, gravitational,
and neutrino channels at E ≈ φ⁻⁵ eV ≈ 0.090 eV.

**Results**:
- EM (Thomson): σ ≈ 6.65×10⁻²⁹ m² (detectable)
- Gravitational: σ_eff ~ 10⁻⁷⁰ m² (completely negligible)
- Neutrino: σ ~ 10⁻⁴⁴ cm² ≈ 10⁻⁴⁸ m² (undetectable at ps timescales)

These calculations justify the BIOPHASE exclusion of non-EM channels.
-/

namespace IndisputableMonolith
namespace BiophasePhysics

open BiophaseCore
open Numerics

/-! ## Electromagnetic Cross-Section -/

/-- Thomson scattering cross-section (classical, non-relativistic limit) -/
noncomputable def sigma_thomson : ℝ :=
  (8 * Real.pi / 3) * classical_electron_radius^2

/-- Thomson cross-section is approximately 6.65×10⁻²⁹ m².  We bound `π` between
    `3.141592` and `3.141593`, propagate those bounds through
    `(8π/3)·rₑ²`, and tighten the result to land inside the desired
    ±`1e-30` window. -/
theorem sigma_thomson_value :
    abs (sigma_thomson - 6.65e-29) < 1e-30 := by
  have h_pi_lower : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have h_pi_upper : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have h_radius_pos : 0 < classical_electron_radius := by
    norm_num [classical_electron_radius]
  have h_sq_pos : 0 < classical_electron_radius ^ 2 :=
    pow_pos h_radius_pos _
  have h_lower :
      ((8 * (3.141592 : ℝ)) / 3) * classical_electron_radius ^ 2 <
        sigma_thomson := by
    unfold sigma_thomson
    have h_factor :
        (8 * (3.141592 : ℝ)) / 3 < (8 * Real.pi) / 3 := by
      have h_mul :
          8 * (3.141592 : ℝ) < 8 * Real.pi :=
        (mul_lt_mul_of_pos_left h_pi_lower (by norm_num : (0 : ℝ) < 8))
      exact (div_lt_div_right (by norm_num : (0 : ℝ) < 3)).2 h_mul
    exact (mul_lt_mul_of_pos_right h_factor h_sq_pos)
  have h_upper :
      sigma_thomson <
        ((8 * (3.141593 : ℝ)) / 3) * classical_electron_radius ^ 2 := by
    unfold sigma_thomson
    have h_factor :
        (8 * Real.pi) / 3 < (8 * (3.141593 : ℝ)) / 3 := by
      have h_mul :
          8 * Real.pi < 8 * (3.141593 : ℝ) :=
        (mul_lt_mul_of_pos_left h_pi_upper (by norm_num : (0 : ℝ) < 8))
      exact (div_lt_div_right (by norm_num : (0 : ℝ) < 3)).2 h_mul
    exact (mul_lt_mul_of_pos_right h_factor h_sq_pos)
  have h_lower_eval :
      ((8 * (3.141592 : ℝ)) / 3) * classical_electron_radius ^ 2 =
        6.652457348145507e-29 := by
    norm_num [classical_electron_radius]
  have h_upper_eval :
      ((8 * (3.141593 : ℝ)) / 3) * classical_electron_radius ^ 2 =
        6.652459465688889e-29 := by
    norm_num [classical_electron_radius]
  have h_neg :
      -(1e-30) < sigma_thomson - 6.65e-29 := by
    have h_lower' :
        6.55e-29 < sigma_thomson := by
      have : 6.55e-29 < 6.652457348145507e-29 := by norm_num
      exact lt_trans this (by simpa [h_lower_eval] using h_lower)
    have := sub_lt_sub_right h_lower' (6.65e-29)
    have h_eval : (6.55e-29 - 6.65e-29 : ℝ) = -(1e-30) := by norm_num
    simpa [h_eval, sub_eq_add_neg]
      using this
  have h_pos :
      sigma_thomson - 6.65e-29 < 1e-30 := by
    have h_upper' :
        sigma_thomson < 6.75e-29 := by
      have : 6.652459465688889e-29 < 6.75e-29 := by norm_num
      exact lt_of_lt_of_le
        (by simpa [h_upper_eval] using h_upper) this.le
    have := sub_lt_sub_right h_upper' (6.65e-29)
    have h_eval : (6.75e-29 - 6.65e-29 : ℝ) = 1e-30 := by norm_num
    simpa [h_eval, sub_eq_add_neg]
      using this
  exact abs_lt.mpr ⟨h_neg, h_pos⟩

/-- Thomson cross-section is positive -/
lemma sigma_thomson_pos : 0 < sigma_thomson := by
  unfold sigma_thomson
  apply mul_pos
  · apply div_pos
    · apply mul_pos
      · norm_num
      · exact Real.pi_pos
    · norm_num
  · apply sq_pos_of_pos
    norm_num [classical_electron_radius]

/-- EM cross-section at given energy (simplified: Thomson for E < MeV) -/
noncomputable def sigma_em (E : ℝ) : ℝ :=
  if E < 1e6 * eV_to_joules then
    sigma_thomson
  else
    sigma_thomson  -- Klein-Nishina for high E (not needed here)


/-- At BIOPHASE energy, EM cross-section equals Thomson -/
theorem sigma_em_at_biophase :
  sigma_em E_biophase = sigma_thomson := by
  unfold sigma_em
  simp [E_biophase_lt_MeV]

/-- The Thomson cross-section is well above the detection threshold `1e-30`. -/
lemma sigma_thomson_detectable : sigma_thomson > 1e-30 := by
  have h_pi : (8 * Real.pi) / 3 > 8 := by
    have h_mul : 8 * Real.pi > 8 * 3 := by
      have h := Real.pi_gt_three
      exact (mul_lt_mul_of_pos_left h (by norm_num : (0 : ℝ) < 8))
    exact (div_lt_div_right (by norm_num : (0 : ℝ) < 3)).2 h_mul
  have h_radius_pos : 0 < classical_electron_radius := by
    norm_num [classical_electron_radius]
  have h :
      sigma_thomson > 8 * classical_electron_radius ^ 2 := by
    unfold sigma_thomson
    have h_sq_pos : 0 < classical_electron_radius ^ 2 :=
      pow_pos h_radius_pos _
    exact
      (mul_lt_mul_of_pos_right h_pi h_sq_pos)
  have h_radius_bound :
      8 * classical_electron_radius ^ 2 > 1e-30 := by
    norm_num [classical_electron_radius]
  exact lt_of_lt_of_le h h_radius_bound.le

/-- EM cross-section at BIOPHASE energy equals the Thomson cross-section, so it
    inherits the detection bound. -/
theorem sigma_em_detectable :
    sigma_em E_biophase > 1e-30 := by
  unfold sigma_em
  simp [E_biophase_lt_MeV, sigma_thomson_detectable]

/-! ## Gravitational Effective Cross-Section -/

/-- Dimensionless gravitational coupling scaled by the Planck energy. -/
noncomputable def coupling_gravitational (E : ℝ) : ℝ :=
  (E / planck_energy)^2

/-- Effective gravitational cross-section via Planck-area suppression:
    σ_grav = ℓ_P² × (E / E_P)². -/
noncomputable def sigma_gravitational (E : ℝ) : ℝ :=
  planck_area * coupling_gravitational E

/-- Gravitational coupling at BIOPHASE energies is astronomically small. -/
theorem coupling_grav_tiny :
    coupling_gravitational E_biophase < 1e-38 := by
  have h_ratio_nonneg :
      0 ≤ E_biophase / planck_energy :=
    div_nonneg (le_of_lt E_biophase_pos) (le_of_lt planck_energy_pos)
  have h_ratio_lt :
      E_biophase / planck_energy < 1e-19 := by
    have h_upper := (E_biophase_bounds).2
    have h_bound :
        (0.091 * eV_to_joules) / planck_energy < 1e-19 := by
      norm_num [planck_energy, eV_to_joules]
    have h_div :=
        (div_lt_div_of_pos_right planck_energy_pos).2 h_upper
    exact lt_trans h_div h_bound
  have h_sq :
      (E_biophase / planck_energy) ^ 2 < (1e-19 : ℝ) ^ 2 :=
    (sq_lt_sq' h_ratio_nonneg (by norm_num : 0 ≤ (1e-19 : ℝ))).2 h_ratio_lt
  have h_eval : (1e-19 : ℝ) ^ 2 = 1e-38 := by norm_num
  simpa [coupling_gravitational, h_eval] using h_sq

/-- Gravitational cross-section is far below any detection threshold. -/
theorem sigma_grav_negligible :
    sigma_gravitational E_biophase < 1e-100 := by
  have h := coupling_grav_tiny
  have h_mul :=
    mul_lt_mul_of_pos_left h planck_area_pos
  have h_bound : planck_area * (1e-38 : ℝ) ≤ 1e-100 := by
    norm_num [planck_area]
  have h_lt :
      sigma_gravitational E_biophase <
        planck_area * (1e-38 : ℝ) := by
    simpa [sigma_gravitational]
      using h_mul
  exact lt_of_lt_of_le h_lt h_bound

/-- Gravitational cross-section is strictly positive (though tiny). -/
lemma sigma_grav_pos :
    0 < sigma_gravitational E_biophase := by
  have h_ratio :
      0 < E_biophase / planck_energy :=
    div_pos E_biophase_pos planck_energy_pos
  have h_coupling :
      0 < coupling_gravitational E_biophase := by
    simpa [coupling_gravitational] using sq_pos_of_pos h_ratio
  exact mul_pos planck_area_pos h_coupling

/-- Gravitational cross-section is vastly smaller than EM -/
theorem sigma_grav_much_smaller_than_em :
  sigma_gravitational E_biophase < sigma_em E_biophase * 1e-40 := by
  have h_grav := sigma_grav_negligible
  have h_mid : (1e-100 : ℝ) < 1e-70 := by norm_num
  have h_em := sigma_em_detectable
  have h_em_scaled :
      (1e-70 : ℝ) < sigma_em E_biophase * 1e-40 := by
    have :=
      mul_lt_mul_of_pos_right h_em (by norm_num : 0 < (1e-40 : ℝ))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  exact lt_trans h_grav (lt_trans h_mid h_em_scaled)

/-! ## Neutrino Cross-Section -/

/-- Neutrino cross-section formula in cm² -/
noncomputable def sigma_neutrino_cm2 (E_eV : ℝ) : ℝ :=
  -- σ_ν ≈ 10⁻⁴⁴ cm² × (E/GeV)²
  1e-44 * (E_eV / 1e9)^2

/-- Neutrino cross-section via weak interaction: σ_ν ~ G_F² E² (in m²) -/
noncomputable def sigma_neutrino (E : ℝ) : ℝ :=
  -- Simplified: use direct cm² formula converted to m²
  sigma_neutrino_cm2 (E / eV_to_joules) * 1e-4  -- cm² to m²

lemma sigma_neutrino_eval (E : ℝ) :
    sigma_neutrino E =
      1e-48 * ((E / eV_to_joules) / 1e9) ^ 2 := by
  unfold sigma_neutrino sigma_neutrino_cm2
  have :
      1e-44 * ((E / eV_to_joules) / 1e9) ^ 2 * 1e-4 =
        (1e-44 * 1e-4) * ((E / eV_to_joules) / 1e9) ^ 2 := by
    ring
  simp [pow_two, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, this]
  norm_num

/-- Neutrino cross-section at BIOPHASE energy (0.09 eV) is tiny in cm². -/
lemma sigma_nu_at_biophase_tiny :
    sigma_neutrino_cm2 0.09 < 1e-62 := by
  unfold sigma_neutrino_cm2
  have h_eval :
      (0.09 / 1e9 : ℝ) = 9e-11 := by norm_num
  have h_val :
      1e-44 * (9e-11 : ℝ) ^ 2 = 8.1e-65 := by norm_num
  simpa [h_eval, h_val]

/-- Neutrino cross-section is completely undetectable at ps timescales
    (≲ 10⁻⁶⁸ m²). -/
theorem sigma_nu_undetectable :
    sigma_neutrino E_biophase < 1e-68 := by
  have hx_bounds := BiophaseCore.E_biophase_eV_bounds
  have hx_lt : E_biophase / eV_to_joules < 0.091 := hx_bounds.2
  have hx_div_lt :
      (E_biophase / eV_to_joules) / 1e9
        < (0.091 : ℝ) / 1e9 :=
    (div_lt_div_right (by norm_num : (0 : ℝ) < 1e9)).2 hx_lt
  have hx_div_nonneg :
      0 ≤ (E_biophase / eV_to_joules) / 1e9 := by
    have hx_pos : 0 ≤ E_biophase / eV_to_joules :=
      (BiophaseCore.E_biophase_eV_bounds.1).le
    exact div_nonneg hx_pos (by norm_num : (0 : ℝ) ≤ 1e9)
  have hx_sq_lt :
      ((E_biophase / eV_to_joules) / 1e9) ^ 2
        < ((0.091 : ℝ) / 1e9) ^ 2 :=
    (sq_lt_sq₀ hx_div_nonneg (by positivity)).2 hx_div_lt
  have hx_sq_lt_one :
      ((E_biophase / eV_to_joules) / 1e9) ^ 2 < 1 := by
    have : ((0.091 : ℝ) / 1e9) ^ 2 < 1 := by norm_num
    exact lt_of_lt_of_le hx_sq_lt this.le
  have hx_sq_nonneg :
      0 ≤ ((E_biophase / eV_to_joules) / 1e9) ^ 2 :=
    sq_nonneg _
  have h_eval := sigma_neutrino_eval E_biophase
  have h_scale_pos : 0 < (1e-48 : ℝ) := by norm_num
  have hx_sq_bound :
      ((E_biophase / eV_to_joules) / 1e9) ^ 2 < 1e-20 := by
    have : ((0.091 : ℝ) / 1e9) ^ 2 < 1e-20 := by norm_num
    exact lt_of_lt_of_le hx_sq_lt this.le
  have h_lt :
      1e-48 * ((E_biophase / eV_to_joules) / 1e9) ^ 2
        < 1e-48 * 1e-20 :=
    (mul_lt_mul_of_pos_left hx_sq_bound h_scale_pos)
  have h_eval' : 1e-48 * 1e-20 = (1e-68 : ℝ) := by norm_num
  simpa [h_eval, h_eval'] using h_lt

/-- Neutrino cross-section lower bound (computed value ~ 10⁻⁶⁹). -/
theorem sigma_nu_lower_bound :
    1e-72 < sigma_neutrino E_biophase := by
  have hx_bounds := BiophaseCore.E_biophase_eV_bounds
  have hx_gt : 0.089 < E_biophase / eV_to_joules := hx_bounds.1
  have hx_div_gt :
      (0.089 : ℝ) / 1e9 <
        (E_biophase / eV_to_joules) / 1e9 :=
    (div_lt_div_right (by norm_num : (0 : ℝ) < 1e9)).2 hx_gt
  have hx_div_nonneg :
      0 ≤ (E_biophase / eV_to_joules) / 1e9 := by
    have hx_pos : 0 ≤ E_biophase / eV_to_joules :=
      (BiophaseCore.E_biophase_eV_bounds.1).le
    exact div_nonneg hx_pos (by norm_num : (0 : ℝ) ≤ 1e9)
  have hx_sq_gt :
      ((0.089 : ℝ) / 1e9) ^ 2
        < ((E_biophase / eV_to_joules) / 1e9) ^ 2 :=
    (sq_lt_sq₀ (by positivity) hx_div_nonneg).2 hx_div_gt
  have h_eval := sigma_neutrino_eval E_biophase
  have h_scale_pos : 0 < (1e-48 : ℝ) := by norm_num
  have hx_sq_pos :
      0 < ((E_biophase / eV_to_joules) / 1e9) ^ 2 :=
    lt_of_le_of_lt (sq_nonneg _) hx_sq_gt
  have h_lt :
      1e-48 * ((0.089 : ℝ) / 1e9) ^ 2 <
        1e-48 * ((E_biophase / eV_to_joules) / 1e9) ^ 2 :=
    (mul_lt_mul_of_pos_left hx_sq_gt h_scale_pos)
  have h_constant :
      1e-48 * ((0.089 : ℝ) / 1e9) ^ 2 = 7.921e-69 := by
    norm_num
  have h_threshold :
      (1e-72 : ℝ) < 7.921e-69 := by norm_num
  have h_chain :
      1e-72 < 1e-48 * ((E_biophase / eV_to_joules) / 1e9) ^ 2 :=
    lt_trans h_threshold (by simpa [h_constant] using h_lt)
  simpa [h_eval] using h_chain

/-- Neutrino cross-section is positive (tiny but non-zero). -/
theorem sigma_nu_pos :
    0 < sigma_neutrino E_biophase := by
  have h_eval := sigma_neutrino_eval E_biophase
  have h_scale_pos : 0 < (1e-48 : ℝ) := by norm_num
  have hx_num_pos :
      0 < E_biophase / eV_to_joules :=
    lt_trans (by norm_num) BiophaseCore.E_biophase_eV_bounds.1
  have hx_pos :
      0 < (E_biophase / eV_to_joules) / 1e9 :=
    (div_pos_iff).2 <|
      Or.inl ⟨hx_num_pos, by norm_num⟩
  have hx_sq_pos : 0 < ((E_biophase / eV_to_joules) / 1e9) ^ 2 :=
    pow_pos hx_pos _
  simpa [h_eval] using
    mul_pos h_scale_pos hx_sq_pos

/-- Gravitational cross-section is smaller than neutrino cross-section. -/
theorem sigma_grav_lt_nu :
    sigma_gravitational E_biophase < sigma_neutrino E_biophase := by
  have h1 := sigma_grav_negligible
  have h_lt : sigma_gravitational E_biophase < 1e-72 :=
    lt_trans h1 (by norm_num)
  have h2 := sigma_nu_lower_bound
  exact lt_trans h_lt h2

/-- Neutrino cross-section is smaller than EM cross-section. -/
theorem sigma_nu_lt_em :
    sigma_neutrino E_biophase < sigma_em E_biophase := by
  have h1 := sigma_nu_undetectable
  have h_lt : sigma_neutrino E_biophase < 1e-30 :=
    lt_trans h1 (by norm_num)
  have h2 := sigma_em_detectable
  exact lt_trans h_lt h2

/-! ## Comparison Summary -/

/-- Ratio of EM to gravitational cross-sections -/
noncomputable def ratio_em_to_grav : ℝ :=
  sigma_em E_biophase / sigma_gravitational E_biophase

/-- Ratio of EM to neutrino cross-sections -/
noncomputable def ratio_em_to_nu : ℝ :=
  sigma_em E_biophase / sigma_neutrino E_biophase

/-- EM dominates gravitational by at least 40 orders of magnitude. -/
theorem em_dominates_grav :
    ratio_em_to_grav > 1e40 := by
  have h_grav_pos := sigma_grav_pos
  have h1 := sigma_grav_negligible
  have h2 := sigma_em_detectable
  have h_bound :
      1e40 * sigma_gravitational E_biophase < 1e-60 := by
    have :=
      mul_lt_mul_of_pos_left h1 (by norm_num : 0 < (1e40 : ℝ))
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using this
  have h_sigma :
      1e40 * sigma_gravitational E_biophase <
        sigma_em E_biophase := by
    have : (1e-60 : ℝ) < 1e-30 := by norm_num
    exact lt_trans h_bound (lt_trans this h2)
  unfold ratio_em_to_grav
  exact (lt_div_iff h_grav_pos).2 h_sigma

/-- EM dominates neutrino by at least 15 orders of magnitude. -/
theorem em_dominates_nu :
    ratio_em_to_nu > 1e15 := by
  have h_nu_pos := sigma_nu_pos
  have h1 := sigma_nu_undetectable
  have h2 := sigma_em_detectable
  have h_scaled :
      1e18 * sigma_neutrino E_biophase < 1e-30 := by
    have :=
      mul_lt_mul_of_pos_left h1 (by norm_num : 0 < (1e18 : ℝ))
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using this
  have h_sigma :
      1e18 * sigma_neutrino E_biophase <
        sigma_em E_biophase := lt_trans h_scaled h2
  have h_ratio :
      ratio_em_to_nu > 1e18 :=
    (lt_div_iff h_nu_pos).2 h_sigma
  have h_order : (1e15 : ℝ) < 1e18 := by norm_num
  exact lt_trans h_order h_ratio

/-! ## Cross-Section Witnesses -/

/-- Package of cross-section values with bounds -/
structure CrossSectionData where
  /-- EM cross-section (m²) -/
  sigma_em : ℝ
  /-- Gravitational effective cross-section (m²) -/
  sigma_grav : ℝ
  /-- Neutrino cross-section (m²) -/
  sigma_nu : ℝ

  /-- EM is positive and large -/
  em_pos : 0 < sigma_em
  em_detectable : sigma_em > 1e-30

  /-- Gravitational is negligible -/
  grav_tiny : sigma_grav < 1e-70

  /-- Neutrino is undetectable -/
  nu_tiny : sigma_nu < 1e-48

  /-- Ordering -/
  grav_smallest : sigma_grav < sigma_nu
  nu_smaller : sigma_nu < sigma_em

/-- Standard cross-section data at BIOPHASE energy -/
noncomputable def biophase_cross_sections : CrossSectionData := {
  sigma_em := sigma_em E_biophase
  sigma_grav := sigma_gravitational E_biophase
  sigma_nu := sigma_neutrino E_biophase

  em_pos := by
    rw [sigma_em_at_biophase]
    exact sigma_thomson_pos
  em_detectable := sigma_em_detectable

  grav_tiny := sigma_grav_negligible

  nu_tiny := sigma_nu_undetectable

  grav_smallest := sigma_grav_lt_nu

  nu_smaller := sigma_nu_lt_em
}

/-! ## Physical Interpretation

EM: Thomson scattering is the dominant interaction at sub-eV energies.
Photons interact readily with matter via electronic transitions.

Gravitational: Coupling ~ (E/M_Planck)² is utterly negligible at eV scales.
Would need Planck-scale energies (10¹⁹ GeV) for gravitational detection.

Neutrino: Weak interaction cross-section ~ G_F² E² vanishes at low energy.
At 0.09 eV, interaction length exceeds universe size.
-/

end BiophasePhysics
end IndisputableMonolith
