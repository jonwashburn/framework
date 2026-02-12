import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Numerics.Interval

/-!
# BIOPHASE Physical Constants

Fundamental constants for the BIOPHASE interface derived from φ⁻⁵ eV
and standard physical constants (CODATA 2024).

**Key Values** (from Source.txt @BIOPHASE):
- E_rec ≈ φ⁻⁵ eV ≈ 0.090 eV
- λ₀ ≈ 13.8 μm (IR wavelength)
- ν₀ ≈ 724 cm⁻¹ (wavenumber)
- τ_gate ≈ 65 ps (gating/coherence time)
- T_spectral ≈ 46 fs (h/E_rec)

All numerical values use SI units and CODATA 2024 constants.
-/

namespace IndisputableMonolith
namespace BiophaseCore

open Constants
open Numerics

/-! ## Fundamental Physical Constants (CODATA 2024) -/

/-- Planck constant (J·s) -/
def planck_h : ℝ := 6.62607015e-34

/-- Speed of light (m/s) -/
def speed_of_light : ℝ := 299792458

/-- Electron volt to joules conversion -/
def eV_to_joules : ℝ := 1.602176634e-19

/-- Gravitational constant (m³/kg/s²) -/
def gravitational_constant : ℝ := 6.67430e-11

/-- Fermi constant (GeV⁻²) -/
def G_fermi : ℝ := 1.1663787e-5

/-- Classical electron radius (m) -/
def classical_electron_radius : ℝ := 2.8179403262e-15

/-! ## BIOPHASE Energy Scale -/

/-- Recognition energy: φ⁻⁵ eV in joules -/
noncomputable def E_biophase : ℝ := phi ^ (-(5 : ℝ)) * eV_to_joules

/-- Numerical value of φ⁻⁵ proven via interval arithmetic -/
theorem phi_inv5_value : abs (phi ^ (-(5 : ℝ)) - 0.0901699437) < 1e-9 :=
  phi_inv5_approx

/-- E_biophase is approximately 0.090 eV
    Follows from phi_inv5_value; E_biophase/eV_to_joules = φ⁻⁵ ≈ 0.0901699437 ≈ 0.090
    NOTE: This is a small numeric bound derived directly from `phi_inv5_value`. -/
theorem E_biophase_approx : abs (E_biophase / eV_to_joules - 0.090) < 0.001 := by
  -- E_biophase/eV_to_joules = φ⁻⁵ (since eV_to_joules ≠ 0)
  have hden : (eV_to_joules : ℝ) ≠ 0 := by
    norm_num [eV_to_joules]
  have hdiv : E_biophase / eV_to_joules = phi ^ (-(5 : ℝ)) := by
    unfold E_biophase
    simpa using (mul_div_cancel_right₀ (phi ^ (-(5 : ℝ))) hden)
  -- Reduce to bounding φ⁻⁵ near 0.090 using the existing tight approximation.
  have hφ := phi_inv5_value
  have habs := abs_lt.mp hφ
  have : abs (phi ^ (-(5 : ℝ)) - 0.090) < 0.001 := by
    -- φ⁻⁵ ∈ (0.0901699437 - 1e-9, 0.0901699437 + 1e-9),
    -- so |φ⁻⁵ - 0.090| < 0.001 by linear arithmetic.
    rw [abs_lt]
    constructor <;> linarith
  simpa [hdiv] using this

/-- E_biophase is positive -/
lemma E_biophase_pos : 0 < E_biophase := by
  unfold E_biophase
  apply mul_pos
  · exact Real.rpow_pos_of_pos phi_pos _
  · norm_num [eV_to_joules]

/-! ## Wavelength and Frequency -/

/-- IR wavelength: λ₀ = hc/E (meters) -/
noncomputable def lambda_biophase : ℝ :=
  planck_h * speed_of_light / E_biophase

/-- λ₀ is approximately 13.8 μm
    Computed as: λ = hc/E = (6.626e-34 * 2.998e8) / (0.090 * 1.602e-19)
                         ≈ 1.986e-25 / 1.442e-20 ≈ 13.77e-6 m -/
theorem lambda_biophase_approx : abs (lambda_biophase - 13.8e-6) < 0.5e-6 := by
  -- Bound φ⁻⁵ tightly, then propagate through λ = (h*c)/(φ⁻⁵ * eV).
  have hφ := phi_inv5_value
  have habs := abs_lt.mp hφ
  have hl : (0.0901699437 - 1e-9) < phi ^ (-(5 : ℝ)) := by
    linarith [habs.1]
  have hu : phi ^ (-(5 : ℝ)) < (0.0901699437 + 1e-9) := by
    linarith [habs.2]
  have heVpos : 0 < eV_to_joules := by
    norm_num [eV_to_joules]
  have hEpos : 0 < E_biophase := E_biophase_pos
  have hE_low : (0.0901699437 - 1e-9) * eV_to_joules < E_biophase := by
    unfold E_biophase
    -- multiply the lower φ⁻⁵ bound by the positive conversion factor
    exact mul_lt_mul_of_pos_right hl heVpos
  have hE_high : E_biophase < (0.0901699437 + 1e-9) * eV_to_joules := by
    unfold E_biophase
    exact mul_lt_mul_of_pos_right hu heVpos

  -- It suffices to show: 13.3e-6 < λ < 14.3e-6.
  rw [abs_lt]
  constructor
  · -- Lower: 13.3e-6 < λ
    have h₁ : (13.3e-6 : ℝ) * E_biophase < planck_h * speed_of_light := by
      have hscale : (13.3e-6 : ℝ) * E_biophase < (13.3e-6 : ℝ) * ((0.0901699437 + 1e-9) * eV_to_joules) :=
        mul_lt_mul_of_pos_left hE_high (by norm_num)
      have hnum :
          (13.3e-6 : ℝ) * ((0.0901699437 + 1e-9) * eV_to_joules) < planck_h * speed_of_light := by
        norm_num [planck_h, speed_of_light, eV_to_joules]
      exact lt_trans hscale hnum
    have hEne : (E_biophase : ℝ) ≠ 0 := ne_of_gt hEpos
    have hcancel : ((planck_h * speed_of_light) / E_biophase) * E_biophase = planck_h * speed_of_light := by
      calc
        ((planck_h * speed_of_light) / E_biophase) * E_biophase
            = (planck_h * speed_of_light) * E_biophase / E_biophase := by
                simpa using (div_mul_eq_mul_div (planck_h * speed_of_light) E_biophase E_biophase)
        _ = planck_h * speed_of_light := by
              simpa using (mul_div_cancel_right₀ (planck_h * speed_of_light) hEne)
    have hcomp : (13.3e-6 : ℝ) * E_biophase < ((planck_h * speed_of_light) / E_biophase) * E_biophase := by
      -- Rewrite the RHS to `planck_h * speed_of_light` using `hcancel` and use `h₁`.
      simpa [hcancel] using h₁
    have hlt : (13.3e-6 : ℝ) < (planck_h * speed_of_light) / E_biophase :=
      lt_of_mul_lt_mul_right hcomp (le_of_lt hEpos)
    have hlow : (13.3e-6 : ℝ) < lambda_biophase := by simpa [lambda_biophase] using hlt
    -- Goal is `-(0.5e-6) < lambda_biophase - 13.8e-6`,
    -- which follows from `13.3e-6 < lambda_biophase` since `13.3e-6 = 13.8e-6 - 0.5e-6`.
    linarith
  · -- Upper: λ < 14.3e-6
    have h₂ : planck_h * speed_of_light < (14.3e-6 : ℝ) * E_biophase := by
      have hscale :
          planck_h * speed_of_light < (14.3e-6 : ℝ) * ((0.0901699437 - 1e-9) * eV_to_joules) := by
        norm_num [planck_h, speed_of_light, eV_to_joules]
      have hmono :
          (14.3e-6 : ℝ) * ((0.0901699437 - 1e-9) * eV_to_joules) < (14.3e-6 : ℝ) * E_biophase :=
        mul_lt_mul_of_pos_left hE_low (by norm_num)
      exact lt_trans hscale hmono
    have hEne : (E_biophase : ℝ) ≠ 0 := ne_of_gt hEpos
    have hcancel : ((planck_h * speed_of_light) / E_biophase) * E_biophase = planck_h * speed_of_light := by
      calc
        ((planck_h * speed_of_light) / E_biophase) * E_biophase
            = (planck_h * speed_of_light) * E_biophase / E_biophase := by
                simpa using (div_mul_eq_mul_div (planck_h * speed_of_light) E_biophase E_biophase)
        _ = planck_h * speed_of_light := by
              simpa using (mul_div_cancel_right₀ (planck_h * speed_of_light) hEne)
    have hcomp :
        ((planck_h * speed_of_light) / E_biophase) * E_biophase < (14.3e-6 : ℝ) * E_biophase := by
      -- Rewrite the LHS to `planck_h * speed_of_light` using `hcancel` and use `h₂`.
      simpa [hcancel] using h₂
    have hlt : (planck_h * speed_of_light) / E_biophase < (14.3e-6 : ℝ) :=
      lt_of_mul_lt_mul_right hcomp (le_of_lt hEpos)
    have hup : lambda_biophase < (14.3e-6 : ℝ) := by
      simpa [lambda_biophase] using hlt
    -- Goal is `lambda_biophase - 13.8e-6 < 0.5e-6`,
    -- which follows from `lambda_biophase < 14.3e-6` since `14.3e-6 = 13.8e-6 + 0.5e-6`.
    linarith

/-- λ₀ is positive -/
lemma lambda_biophase_pos : 0 < lambda_biophase := by
  unfold lambda_biophase
  apply div_pos
  · apply mul_pos
    · norm_num [planck_h]
    · norm_num [speed_of_light]
  · exact E_biophase_pos

/-! ## Wavenumber -/

/-- Wavenumber: ν₀ = 1/(λ₀ · 100) in cm⁻¹ -/
noncomputable def nu0_cm1 : ℝ := 1 / (lambda_biophase * 100)

/-- ν₀ is approximately 724 cm⁻¹
    Computed as: ν = 1/(λ·100) = 1/(13.8e-6 * 100) ≈ 724.6 cm⁻¹
    Derived from lambda_biophase_approx. -/
theorem nu0_approx_724 : abs (nu0_cm1 - 724) < 10 := by
  -- Rewrite ν₀ in terms of energy: ν̃(cm⁻¹) = E / (h c · 100).
  have hEpos : 0 < E_biophase := E_biophase_pos
  have hEne : (E_biophase : ℝ) ≠ 0 := ne_of_gt hEpos
  have hhc_pos : 0 < planck_h * speed_of_light := by
    apply mul_pos <;> norm_num [planck_h, speed_of_light]
  have hhc100_pos : 0 < planck_h * speed_of_light * 100 := by
    have : 0 < (100 : ℝ) := by norm_num
    exact mul_pos hhc_pos this
  have hhc100_ne : (planck_h * speed_of_light * 100 : ℝ) ≠ 0 := ne_of_gt hhc100_pos

  have hnu_eq : nu0_cm1 = E_biophase / (planck_h * speed_of_light * 100) := by
    -- nu0_cm1 = 1/(lambda_biophase*100) = 1/((h*c/E)*100) = E/(h*c*100)
    unfold nu0_cm1 lambda_biophase
    -- First rewrite (h*c/E)*100 as (h*c*100)/E.
    have hmul : (planck_h * speed_of_light / E_biophase) * 100 =
        (planck_h * speed_of_light * 100) / E_biophase := by
      -- (a/b)*c = (a*c)/b
      simpa [mul_assoc] using (div_mul_eq_mul_div (planck_h * speed_of_light) E_biophase 100)
    -- Now invert the division.
    -- 1 / ((hc*100)/E) = E / (hc*100)
    calc
      1 / ((planck_h * speed_of_light / E_biophase) * 100)
          = 1 / ((planck_h * speed_of_light * 100) / E_biophase) := by
              simp [hmul]
      _ = E_biophase / (planck_h * speed_of_light * 100) := by
          -- Clear denominators; we need hc*100 ≠ 0 and E ≠ 0.
          field_simp [hhc100_ne, hEne]

  -- Bound E_biophase using the tight φ⁻⁵ approximation, then divide by `h c · 100`.
  have hφ := phi_inv5_value
  have habs := abs_lt.mp hφ
  have hl : (0.0901699437 - 1e-9) < phi ^ (-(5 : ℝ)) := by linarith [habs.1]
  have hu : phi ^ (-(5 : ℝ)) < (0.0901699437 + 1e-9) := by linarith [habs.2]
  have heVpos : 0 < eV_to_joules := by norm_num [eV_to_joules]
  have hE_low : (0.0901699437 - 1e-9) * eV_to_joules < E_biophase := by
    unfold E_biophase
    exact mul_lt_mul_of_pos_right hl heVpos
  have hE_high : E_biophase < (0.0901699437 + 1e-9) * eV_to_joules := by
    unfold E_biophase
    exact mul_lt_mul_of_pos_right hu heVpos

  have hlow_div : (0.0901699437 - 1e-9) * eV_to_joules / (planck_h * speed_of_light * 100)
      < nu0_cm1 := by
    -- divide the lower energy bound by positive `h c · 100`
    have : (0.0901699437 - 1e-9) * eV_to_joules / (planck_h * speed_of_light * 100)
        < E_biophase / (planck_h * speed_of_light * 100) :=
      div_lt_div_of_pos_right hE_low hhc100_pos
    simpa [hnu_eq] using this

  have hup_div : nu0_cm1
      < (0.0901699437 + 1e-9) * eV_to_joules / (planck_h * speed_of_light * 100) := by
    have : E_biophase / (planck_h * speed_of_light * 100)
        < (0.0901699437 + 1e-9) * eV_to_joules / (planck_h * speed_of_light * 100) :=
      div_lt_div_of_pos_right hE_high hhc100_pos
    simpa [hnu_eq] using this

  have h714 : (714 : ℝ) < nu0_cm1 := by
    have hnum : (714 : ℝ) < (0.0901699437 - 1e-9) * eV_to_joules / (planck_h * speed_of_light * 100) := by
      norm_num [planck_h, speed_of_light, eV_to_joules]
    exact lt_trans hnum hlow_div

  have h734 : nu0_cm1 < (734 : ℝ) := by
    have hnum : (0.0901699437 + 1e-9) * eV_to_joules / (planck_h * speed_of_light * 100) < (734 : ℝ) := by
      norm_num [planck_h, speed_of_light, eV_to_joules]
    exact lt_trans hup_div hnum

  -- Convert bounds into the `abs` form.
  rw [abs_lt]
  constructor <;> linarith

/-- ν₀ is positive -/
lemma nu0_cm1_pos : 0 < nu0_cm1 := by
  unfold nu0_cm1
  apply div_pos
  · norm_num
  · apply mul_pos lambda_biophase_pos
    norm_num

/-! ## Timing Parameters -/

/-- Gating/coherence time window (seconds) -/
def tau_gate : ℝ := 65e-12

/-- Spectral resolution time: T_spectral = h/E_rec (seconds) -/
noncomputable def T_spectral : ℝ := planck_h / E_biophase

/-- T_spectral is approximately 46 fs
    Computed as: T = h/E = 6.626e-34 / (0.090 * 1.602e-19) ≈ 45.97e-15 s -/
theorem T_spectral_approx : abs (T_spectral - 46e-15) < 10e-15 := by
  -- Bound E_biophase using the tight φ⁻⁵ approximation, then invert to bound T = h/E.
  have hφ := phi_inv5_value
  have habs := abs_lt.mp hφ
  have hl : (0.0901699437 - 1e-9) < phi ^ (-(5 : ℝ)) := by linarith [habs.1]
  have hu : phi ^ (-(5 : ℝ)) < (0.0901699437 + 1e-9) := by linarith [habs.2]
  have heVpos : 0 < eV_to_joules := by norm_num [eV_to_joules]
  have hEpos : 0 < E_biophase := E_biophase_pos
  have hE_low : (0.0901699437 - 1e-9) * eV_to_joules < E_biophase := by
    unfold E_biophase
    exact mul_lt_mul_of_pos_right hl heVpos
  have hE_high : E_biophase < (0.0901699437 + 1e-9) * eV_to_joules := by
    unfold E_biophase
    exact mul_lt_mul_of_pos_right hu heVpos
  have hE_low_pos : 0 < (0.0901699437 - 1e-9 : ℝ) * eV_to_joules := by
    have : 0 < (0.0901699437 - 1e-9 : ℝ) := by norm_num
    exact mul_pos this heVpos
  have hplanck_pos : 0 < planck_h := by
    norm_num [planck_h]

  -- From E_low < E < E_high, we get h/E_high < h/E < h/E_low.
  have hinv_upper : (1 : ℝ) / ((0.0901699437 + 1e-9) * eV_to_joules) < 1 / E_biophase :=
    one_div_lt_one_div_of_lt hEpos hE_high
  have hinv_lower : (1 : ℝ) / E_biophase < 1 / ((0.0901699437 - 1e-9) * eV_to_joules) :=
    one_div_lt_one_div_of_lt hE_low_pos hE_low

  have hT_lower : planck_h / ((0.0901699437 + 1e-9) * eV_to_joules) < T_spectral := by
    have := mul_lt_mul_of_pos_left hinv_upper hplanck_pos
    -- rewrite `planck_h * (1/x)` as `planck_h / x`
    simpa [T_spectral, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

  have hT_upper : T_spectral < planck_h / ((0.0901699437 - 1e-9) * eV_to_joules) := by
    have := mul_lt_mul_of_pos_left hinv_lower hplanck_pos
    simpa [T_spectral, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

  -- Show: 36e-15 < T_spectral < 56e-15, then conclude `|T - 46e-15| < 10e-15`.
  have h36 : (36e-15 : ℝ) < planck_h / ((0.0901699437 + 1e-9) * eV_to_joules) := by
    norm_num [planck_h, eV_to_joules]
  have h56 : planck_h / ((0.0901699437 - 1e-9) * eV_to_joules) < (56e-15 : ℝ) := by
    norm_num [planck_h, eV_to_joules]
  have hT_lt : (36e-15 : ℝ) < T_spectral ∧ T_spectral < (56e-15 : ℝ) := by
    constructor
    · exact lt_trans h36 hT_lower
    · exact lt_trans hT_upper h56

  -- Convert the interval bound into the requested absolute-value tolerance.
  rcases hT_lt with ⟨hlo, hhi⟩
  rw [abs_lt]
  constructor <;> linarith

/-- T_spectral is positive -/
lemma T_spectral_pos : 0 < T_spectral := by
  unfold T_spectral
  apply div_pos
  · norm_num [planck_h]
  · exact E_biophase_pos

/-! ## Cycle Structure -/

/-- Breath cycle period (ticks) -/
def breath_period : ℕ := 1024

/-- FLIP instruction position in cycle -/
def flip_at_tick : ℕ := 512

/-- Breath period is 2^10 -/
lemma breath_is_pow2 : breath_period = 2^10 := by norm_num [breath_period]

/-- FLIP is at midpoint -/
lemma flip_at_midpoint : flip_at_tick * 2 = breath_period := by
  norm_num [flip_at_tick, breath_period]

/-! ## Energy-Frequency Relations -/

/-- Photon energy E = hν -/
noncomputable def photon_energy (freq_hz : ℝ) : ℝ := planck_h * freq_hz

/-- Wavelength from energy: λ = hc/E -/
noncomputable def wavelength_from_energy (E : ℝ) : ℝ :=
  planck_h * speed_of_light / E

/-- Frequency from wavelength: ν = c/λ -/
noncomputable def frequency_from_wavelength (lambda : ℝ) : ℝ :=
  speed_of_light / lambda

/-- Wavenumber from wavelength: ν̃ = 1/λ (in m⁻¹, divide by 100 for cm⁻¹) -/
noncomputable def wavenumber_from_wavelength (lambda : ℝ) : ℝ :=
  1 / lambda

/-! ## Conversion Utilities -/

/-- Convert wavelength (m) to wavenumber (cm⁻¹) -/
noncomputable def lambda_to_nu_cm1 (lambda : ℝ) : ℝ :=
  1 / (lambda * 100)

/-- Convert wavenumber (cm⁻¹) to wavelength (m) -/
noncomputable def nu_cm1_to_lambda (nu : ℝ) : ℝ :=
  1 / (nu * 100)

/-- Convert frequency (Hz) to wavenumber (cm⁻¹) -/
noncomputable def freq_to_nu_cm1 (freq : ℝ) : ℝ :=
  freq / (speed_of_light * 100)

/-- Roundtrip conversion: λ → ν̃ → λ -/
lemma lambda_nu_roundtrip (lambda : ℝ) (h : 0 < lambda) :
  nu_cm1_to_lambda (lambda_to_nu_cm1 lambda) = lambda := by
  unfold nu_cm1_to_lambda lambda_to_nu_cm1
  field_simp [h]

/-! ## Summary Witness -/

/-- Package of all BIOPHASE constants with proofs -/
structure BiophaseConstants where
  E_rec : ℝ
  lambda0 : ℝ
  nu0 : ℝ
  tau_gate : ℝ
  T_spectral : ℝ
  breath : ℕ
  flip_tick : ℕ

  E_pos : 0 < E_rec
  lambda_pos : 0 < lambda0
  nu_pos : 0 < nu0
  tau_pos : 0 < tau_gate
  T_pos : 0 < T_spectral

  E_approx : abs (E_rec / eV_to_joules - 0.090) < 0.001
  lambda_approx : abs (lambda0 - 13.8e-6) < 0.5e-6
  nu_approx : abs (nu0 - 724) < 10

  breath_val : breath = 1024
  flip_val : flip_tick = 512

/-- Tolerance parameters for BIOPHASE acceptance checks.
    - `delta_lambda_um`: allowed deviation in wavelength (μm)
    - `delta_nu_cm1`: allowed deviation in wavenumber (cm⁻¹)
    - `timing_jitter_ps`: allowed timing jitter (ps)
 -/
structure Tolerances where
  delta_lambda_um : ℝ
  delta_nu_cm1 : ℝ
  timing_jitter_ps : ℝ

/-- Standard tolerances used in BIOPHASE reports. -/
def standard_tolerances : Tolerances :=
  { delta_lambda_um := 0.5
  , delta_nu_cm1 := 10.0
  , timing_jitter_ps := 5.0 }

/-- Standard BIOPHASE constants -/
noncomputable def standard_biophase_constants : BiophaseConstants := {
  E_rec := E_biophase
  lambda0 := lambda_biophase
  nu0 := nu0_cm1
  tau_gate := tau_gate
  T_spectral := T_spectral
  breath := breath_period
  flip_tick := flip_at_tick

  E_pos := E_biophase_pos
  lambda_pos := lambda_biophase_pos
  nu_pos := nu0_cm1_pos
  tau_pos := by norm_num [tau_gate]
  T_pos := T_spectral_pos

  E_approx := E_biophase_approx
  lambda_approx := lambda_biophase_approx
  nu_approx := nu0_approx_724

  breath_val := rfl
  flip_val := rfl
}

end BiophaseCore
end IndisputableMonolith
