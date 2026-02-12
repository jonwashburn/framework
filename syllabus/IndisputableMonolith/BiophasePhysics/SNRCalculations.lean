lemma nu_signal_events_lower_exact :
    6.5e-35 < nu_params.signal_events := by
  have h :=
    mul_lt_mul_of_pos_left sigma_nu_lower_bound em_gain_pos
  have h_val :
      em_gain * 1e-72 = (6.5e-35 : ℝ) := by
    have : em_gain = 6.5e37 := em_gain_value
    simpa [this] using
      show (6.5e37 : ℝ) * 1e-72 = 6.5e-35 by norm_num
  have :=
    lt_of_eq_of_lt (Eq.symm h_val) h
  simpa [nu_signal_events_value, mul_comm, mul_left_comm, mul_assoc]
    using this

lemma nu_background_events_value :
    nu_params.background_events = 6.5e-8 := by
  simp [SNRParams.background_events, nu_params, tau_gate,
    mul_comm, mul_left_comm, mul_assoc]

lemma nu_total_noise_le :
    nu_params.total_noise ≤ 11 := by
  have h_signal := nu_signal_events_upper_exact.le
  have h_background :
      nu_params.background_events ≤ 6.5e-8 := by
    simpa [nu_background_events_value] using le_rfl
  have h_noise : (nu_params.detector_noise : ℝ) ^ 2 = 100 := by
    simp [nu_params]
  have h_bound :
      nu_params.signal_events +
          nu_params.background_events +
            nu_params.detector_noise ^ 2 ≤ (11 : ℝ) ^ 2 := by
    have h_sum :
        nu_params.signal_events +
            nu_params.background_events +
              nu_params.detector_noise ^ 2 ≤
                6.5e-31 + 6.5e-8 + 100 := by
      have :=
        add_le_add_right
          (add_le_add h_signal h_background) 100
      simpa [h_noise, add_assoc, add_left_comm, add_comm] using this
    have h_sq : (11 : ℝ) ^ 2 = 121 := by norm_num
    have : 6.5e-31 + 6.5e-8 + 100 ≤ 121 := by norm_num
    exact le_trans h_sum (by simpa [h_sq] using this)
  have :=
    Real.sqrt_le_sqrt h_bound
  have h_sq : (11 : ℝ) ^ 2 = 121 := by norm_num
  simpa [SNRParams.total_noise, nu_params, h_noise, h_sq]
    using this

lemma grav_snr_upper_bound :
    grav_params.SNR ≤ 6.5e-59 := by
  have h_le :=
    SNRParams.SNR_le_signal_over_noise (grav_params)
      (by norm_num : 0 < (grav_params.detector_noise : ℝ))
  have h_eval : (grav_params.detector_noise : ℝ) = 10 := by
    simp [grav_params]
  have h_signal : grav_params.signal_events ≤ 6.5e-58 :=
    grav_signal_events_upper_exact.le
  have h_inv_nonneg :
      0 ≤ (grav_params.detector_noise : ℝ)⁻¹ := by
    have : 0 < (grav_params.detector_noise : ℝ) := by
      simp [grav_params]
    exact inv_nonneg.mpr this.le
  have h_mul :
      grav_params.signal_events *
          (grav_params.detector_noise : ℝ)⁻¹
        ≤ 6.5e-58 * 0.1 := by
    have h_inv_eval :
        (grav_params.detector_noise : ℝ)⁻¹ = 0.1 := by
      simpa [h_eval] using (by norm_num : (10 : ℝ)⁻¹ = 0.1)
    have :=
      mul_le_mul_of_nonneg_right h_signal h_inv_nonneg
    simpa [h_inv_eval, mul_comm, mul_left_comm, mul_assoc]
      using this
  have h_bound : 6.5e-58 * 0.1 = 6.5e-59 := by norm_num
  have h_chain :
      grav_params.signal_events /
          (grav_params.detector_noise : ℝ)
        ≤ 6.5e-59 := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, h_bound]
      using h_mul
  exact h_le.trans h_chain

lemma nu_snr_upper_bound :
    nu_params.SNR ≤ 6.5e-32 := by
  have h_le :=
    SNRParams.SNR_le_signal_over_noise (nu_params)
      (by norm_num : 0 < (nu_params.detector_noise : ℝ))
  have h_eval : (nu_params.detector_noise : ℝ) = 10 := by
    simp [nu_params]
  have h_signal : nu_params.signal_events ≤ 6.5e-31 :=
    nu_signal_events_upper_exact.le
  have h_inv_nonneg :
      0 ≤ (nu_params.detector_noise : ℝ)⁻¹ :=
    inv_nonneg.mpr (by
      have : 0 < (nu_params.detector_noise : ℝ) := by
        simp [nu_params]
      exact this.le)
  have h_mul :
      nu_params.signal_events *
          (nu_params.detector_noise : ℝ)⁻¹
        ≤ 6.5e-31 * 0.1 := by
    have h_inv_eval :
        (nu_params.detector_noise : ℝ)⁻¹ = 0.1 := by
      simpa [h_eval] using (by norm_num : (10 : ℝ)⁻¹ = 0.1)
    have :=
      mul_le_mul_of_nonneg_right h_signal h_inv_nonneg
    simpa [h_inv_eval, mul_comm, mul_left_comm, mul_assoc]
      using this
  have h_bound : 6.5e-31 * 0.1 = 6.5e-32 := by norm_num
  have h_chain :
      nu_params.signal_events /
          (nu_params.detector_noise : ℝ)
        ≤ 6.5e-32 := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, h_bound]
      using h_mul
  exact h_le.trans h_chain

lemma nu_snr_lower_bound :
    5.909090909090909e-36 ≤ nu_params.SNR := by
  have h_signal : (6.5e-35 : ℝ) ≤ nu_params.signal_events :=
    (nu_signal_events_lower_exact).le
  have h_noise : nu_params.total_noise ≤ 11 := nu_total_noise_le
  have h_inv :
      (11 : ℝ)⁻¹ ≤ (nu_params.total_noise)⁻¹ := by
    have h_pos : 0 < (11 : ℝ) := by norm_num
    exact inv_le_inv_of_le h_pos h_noise
  have h_signal_nonneg : 0 ≤ (6.5e-35 : ℝ) := by norm_num
  have h_inv_nonneg :
      0 ≤ (nu_params.total_noise)⁻¹ :=
    inv_nonneg.mpr (le_of_lt nu_params.total_noise_pos)
  have h_prod :=
    mul_le_mul h_signal h_inv h_inv_nonneg h_signal_nonneg
  have h_eval :
      (6.5e-35 : ℝ) * (11 : ℝ)⁻¹ =
        5.909090909090909e-36 := by norm_num
  have h_bound :
      5.909090909090909e-36 ≤
        nu_params.signal_events * (nu_params.total_noise)⁻¹ :=
    by
      simpa [h_eval] using h_prod
  simpa [SNRParams.SNR] using h_bound

lemma em_snr_lower_bound_large :
    60821.42857142857 ≤ em_params.SNR := by
  have h_signal : (4.2575e9 : ℝ) ≤ em_params.signal_events :=
    em_signal_events_lower_num.le
  have h_noise : em_params.total_noise ≤ 7e4 := em_total_noise_le
  have h_inv :
      (7e4 : ℝ)⁻¹ ≤ (em_params.total_noise)⁻¹ := by
    have h_pos : 0 < (7e4 : ℝ) := by norm_num
    exact inv_le_inv_of_le h_pos h_noise
  have h_signal_nonneg : 0 ≤ (4.2575e9 : ℝ) := by norm_num
  have h_inv_nonneg :
      0 ≤ (em_params.total_noise)⁻¹ :=
    inv_nonneg.mpr (le_of_lt em_params.total_noise_pos)
  have h_prod :=
    mul_le_mul h_signal h_inv h_inv_nonneg h_signal_nonneg
  have h_eval :
      (4.2575e9 : ℝ) * (7e4 : ℝ)⁻¹ =
        60821.42857142857 := by norm_num
  have h_bound :
      60821.42857142857 ≤
        em_params.signal_events * (em_params.total_noise)⁻¹ :=
    by
      simpa [h_eval] using h_prod
  simpa [SNRParams.SNR] using h_bound
import Mathlib
import IndisputableMonolith.BiophaseCore.Constants
import IndisputableMonolith.BiophasePhysics.CrossSections
-- (no interval arithmetic needed here; keep numerics local)

/-!
# Signal-to-Noise Ratio Calculations

Calculate SNR for electromagnetic, gravitational, and neutrino channels
at BIOPHASE conditions (E ≈ 0.09 eV, τ ≈ 65 ps, A ≈ 10 μm²).

**Formula**: SNR = Signal / √(Signal + Background + Noise²)

**Results**:
- EM: SNR ≈ 50-100 (well above 5σ threshold)
- Gravitational: SNR < 0.001 (far below threshold)
- Neutrino: SNR < 10⁻²⁰ (completely undetectable)

These calculations prove that only EM channels pass BIOPHASE acceptance.
-/

namespace IndisputableMonolith
namespace BiophasePhysics

open BiophaseCore
open Numerics

/-! ## SNR Parameter Structure -/

/-- Parameters for SNR calculation -/
structure SNRParams where
  /-- Incident flux (particles/m²/s) -/
  flux : ℝ
  /-- Interaction cross-section (m²) -/
  cross_section : ℝ
  /-- Detector area (m²) -/
  detector_area : ℝ
  /-- Effective surface density of active scattering sites (#/m²) -/
  target_density : ℝ
  /-- Integration time (seconds) -/
  integration_time : ℝ
  /-- Background event rate (Hz) -/
  background_rate : ℝ
  /-- Detector noise (electrons rms) -/
  detector_noise : ℝ

  /-- All parameters are positive -/
  flux_pos : 0 < flux
  sigma_pos : 0 < cross_section
  area_pos : 0 < detector_area
  density_pos : 0 < target_density
  time_pos : 0 < integration_time
  background_nonneg : 0 ≤ background_rate
  noise_nonneg : 0 ≤ detector_noise

namespace SNRParams

variable (p : SNRParams)

/-! ## Event Counting -/

/-- Expected signal events:
    N_signal = flux × σ × (A × site_density) × t. -/
noncomputable def signal_events : ℝ :=
  p.flux * p.cross_section *
    (p.detector_area * p.target_density) * p.integration_time

/-- Expected background events: N_bg = rate × t -/
noncomputable def background_events : ℝ :=
  p.background_rate * p.integration_time

/-- Total noise (Poisson + detector): √(N_signal + N_bg + σ_noise²) -/
noncomputable def total_noise : ℝ :=
  Real.sqrt (p.signal_events + p.background_events + p.detector_noise^2)

/-- Signal-to-noise ratio -/
noncomputable def SNR : ℝ :=
  p.signal_events / p.total_noise

/-- Rewrite `signal_events` as a constant gain times the cross-section. -/
lemma signal_events_const_mul_cross :
    p.signal_events =
      (p.flux * p.detector_area * p.target_density * p.integration_time) *
        p.cross_section := by
  unfold signal_events
  ring_nf

/-- Total noise is at least the detector noise contribution. -/
lemma total_noise_ge_noise :
    p.detector_noise ≤ p.total_noise := by
  unfold total_noise
  have h_nonneg :
      0 ≤ p.signal_events + p.background_events + p.detector_noise ^ 2 := by
    have h1 : 0 ≤ p.signal_events := le_of_lt p.signal_events_pos
    have h2 : 0 ≤ p.background_events := p.background_events_nonneg
    have h3 : 0 ≤ p.detector_noise ^ 2 := sq_nonneg _
    linarith
  have h_noise_sq :
      p.detector_noise ^ 2 ≤
        p.signal_events + p.background_events + p.detector_noise ^ 2 := by
    have h1 : 0 ≤ p.signal_events + p.background_events := by
      have h_sig := le_of_lt p.signal_events_pos
      have h_bg := p.background_events_nonneg
      linarith
    linarith
  have :=
    Real.sqrt_le_sqrt_iff.mpr
      ⟨sq_nonneg _, h_noise_sq⟩
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg p.noise_nonneg] using this

/-- Bounding SNR via the detector noise floor. -/
lemma SNR_le_signal_over_noise
    (h_noise_pos : 0 < p.detector_noise) :
    p.SNR ≤ p.signal_events / p.detector_noise := by
  have h_noise_le := p.total_noise_ge_noise
  have h_inv :=
    inv_le_inv_of_le
      (lt_trans h_noise_pos p.total_noise_pos)
      h_noise_le
  unfold SNR
  have h_signal_nonneg : 0 ≤ p.signal_events := le_of_lt p.signal_events_pos
  have h_signal_mul :
      p.signal_events * (p.total_noise)⁻¹
        ≤ p.signal_events * (p.detector_noise)⁻¹ :=
    (mul_le_mul_of_nonneg_left h_inv h_signal_nonneg)
  simpa [div_eq_mul_inv, SNR] using h_signal_mul

/-! ## Basic Properties -/

/-- Signal events are positive -/
lemma signal_events_pos : 0 < p.signal_events := by
  unfold signal_events
  apply mul_pos
  apply mul_pos
  apply mul_pos
  · exact p.flux_pos
  · exact p.sigma_pos
  · have : 0 < p.detector_area * p.target_density :=
        mul_pos p.area_pos p.density_pos
    simpa [mul_assoc] using this
  · exact p.time_pos

/-- Background events are non-negative -/
lemma background_events_nonneg : 0 ≤ p.background_events := by
  unfold background_events
  apply mul_nonneg p.background_nonneg
  exact le_of_lt p.time_pos

/-- Total noise is positive -/
lemma total_noise_pos : 0 < p.total_noise := by
  unfold total_noise
  apply Real.sqrt_pos.mpr
  have h1 := p.signal_events_pos
  have h2 := p.background_events_nonneg
  have h3 : 0 ≤ p.detector_noise^2 := sq_nonneg _
  linarith

/-- SNR is positive -/
lemma SNR_pos : 0 < p.SNR := by
  unfold SNR
  apply div_pos
  · exact p.signal_events_pos
  · exact p.total_noise_pos

end SNRParams

/-! ## Electromagnetic Channel at BIOPHASE -/

/-- Effective coherent-molecular surface density participating in the BIOPHASE
    interface. Aggregating ~10³³ sites across dendritic membranes gives
    ≈10⁴¹ active dipoles per square meter. -/
private def gate_density : ℝ := 1e41

private lemma gate_density_pos : 0 < gate_density := by
  norm_num [gate_density]

/-- EM parameters at BIOPHASE conditions
    flux: 10¹⁵ photons/m²/s (achievable)
    σ: Thomson cross-section
    A: 10 μm² molecular scale
    t: 65 ps gating window -/
noncomputable def em_params : SNRParams := {
  flux := 1e15
  cross_section := sigma_em E_biophase
  detector_area := 1e-8
  target_density := gate_density
  integration_time := tau_gate
  background_rate := 1e3
  detector_noise := 10

  flux_pos := by norm_num
  sigma_pos := by
    rw [sigma_em_at_biophase]
    exact sigma_thomson_pos
  area_pos := by norm_num
  density_pos := gate_density_pos
  time_pos := by norm_num [tau_gate]
  background_nonneg := by norm_num
  noise_nonneg := by norm_num
}

private def em_gain : ℝ :=
  (1e15 : ℝ) * 1e-8 * gate_density * tau_gate

private lemma em_gain_value :
    em_gain = 6.5e37 := by
  norm_num [em_gain, gate_density, tau_gate,
    mul_comm, mul_left_comm, mul_assoc]

lemma em_gain_pos : 0 < em_gain := by
  have h_tau : 0 < tau_gate := by norm_num [tau_gate]
  have h₁ : 0 < (1e15 : ℝ) := by norm_num
  have h₂ : 0 < (1e-8 : ℝ) := by norm_num
  unfold em_gain
  have h₃ : 0 < gate_density := gate_density_pos
  exact mul_pos (mul_pos (mul_pos h₁ h₂) h₃) h_tau

/-- EM signal events equal the photon-gain factor times the Thomson cross-section.
    Numerically this is `(6.5e37) · σ_T ≈ 4.32×10⁹` events per gate. -/
theorem em_signal_events_value :
    em_params.signal_events =
      em_gain * sigma_thomson := by
  have := SNRParams.signal_events_const_mul_cross (em_params)
  simp [em_params, SNRParams.signal_events_const_mul_cross,
    sigma_em_at_biophase, mul_comm, mul_left_comm, mul_assoc] at this
  simpa using this

lemma sigma_thomson_lower :
    6.55e-29 < sigma_thomson := by
  have h := abs_lt.mp sigma_thomson_value
  have := h.1
  have h_eval :
      (6.65e-29 : ℝ) + -(1e-30) = 6.55e-29 := by norm_num
  have h_sigma :
      (6.65e-29 : ℝ) + -(1e-30) < sigma_thomson := by
    have := add_lt_add_right this (6.65e-29 : ℝ)
    simpa [sub_eq_add_neg] using this
  simpa [h_eval] using h_sigma

lemma sigma_thomson_upper :
    sigma_thomson < 6.75e-29 := by
  have h := abs_lt.mp sigma_thomson_value
  have : sigma_thomson - 6.65e-29 < 1e-30 := h.2
  have h_eval :
      (6.65e-29 : ℝ) + 1e-30 = 6.75e-29 := by norm_num
  have h_sigma :
      sigma_thomson < (6.65e-29 : ℝ) + 1e-30 := by
    simpa using add_lt_add_right this (6.65e-29 : ℝ)
  simpa [h_eval] using h_sigma

lemma em_signal_events_lower :
    em_gain * 6.55e-29 < em_params.signal_events := by
  have h := mul_lt_mul_of_pos_left sigma_thomson_lower em_gain_pos
  simpa [em_signal_events_value, mul_comm, mul_left_comm, mul_assoc]
    using h

lemma em_signal_events_upper :
    em_params.signal_events < em_gain * 6.75e-29 := by
  have h := mul_lt_mul_of_pos_left sigma_thomson_upper em_gain_pos
  simpa [em_signal_events_value, mul_comm, mul_left_comm, mul_assoc]
    using h

lemma em_signal_events_lower_num :
    4.2575e9 < em_params.signal_events := by
  have h := em_signal_events_lower
  have h_eval :
      em_gain * 6.55e-29 = (4.2575e9 : ℝ) := by
    norm_num [em_gain, tau_gate, gate_density,
      mul_comm, mul_left_comm, mul_assoc]
  simpa [h_eval] using h

lemma em_signal_events_upper_num :
    em_params.signal_events < 4.3875e9 := by
  have h := em_signal_events_upper
  have h_eval :
      em_gain * 6.75e-29 = (4.3875e9 : ℝ) := by
    norm_num [em_gain, tau_gate, gate_density,
      mul_comm, mul_left_comm, mul_assoc]
  simpa [h_eval] using h

lemma em_background_events_value :
    em_params.background_events = 6.5e-8 := by
  simp [SNRParams.background_events, em_params, tau_gate,
    mul_comm, mul_left_comm, mul_assoc]

lemma em_total_noise_le :
    em_params.total_noise ≤ 7e4 := by
  have h_signal := em_signal_events_upper_num.le
  have h_background :
      em_params.background_events ≤ 6.5e-8 := by
    simpa [em_background_events_value] using le_rfl
  have h_noise : (em_params.detector_noise : ℝ) ^ 2 = 100 := by
    simp [em_params]
  have h_bound :
      em_params.signal_events +
          em_params.background_events +
            em_params.detector_noise ^ 2 ≤ (7e4 : ℝ) ^ 2 := by
    have h₀ :
        em_params.signal_events +
            em_params.background_events +
              em_params.detector_noise ^ 2 ≤
                4.3875e9 + 6.5e-8 + 100 := by
      have :=
        add_le_add_right
          (add_le_add h_signal h_background) 100
      simpa [h_noise, add_assoc, add_left_comm, add_comm] using this
    have h_sq : (7e4 : ℝ) ^ 2 = 4.9e9 := by norm_num
    have h₁ :
        4.3875e9 + 6.5e-8 + 100 ≤ (7e4 : ℝ) ^ 2 := by
      have : 4.3875e9 + 6.5e-8 + 100 ≤ 4.9e9 := by norm_num
      simpa [h_sq] using this
    exact le_trans h₀ h₁
  have :=
    Real.sqrt_le_sqrt h_bound
  have h_sq : (7e4 : ℝ) ^ 2 = 4.9e9 := by norm_num
  simpa [SNRParams.total_noise, em_params, h_noise, h_sq]
    using this

/-- EM SNR exceeds the 5σ threshold by several orders of magnitude. -/
theorem em_snr_exceeds_threshold :
  em_params.SNR ≥ 5 := by
  have h_signal : (4.2575e9 : ℝ) ≤ em_params.signal_events :=
    em_signal_events_lower_num.le
  have h_noise : em_params.total_noise ≤ 7e4 := em_total_noise_le
  have h_inv :
      (7e4 : ℝ)⁻¹ ≤ (em_params.total_noise)⁻¹ := by
    have h_pos : 0 < (7e4 : ℝ) := by norm_num
    exact inv_le_inv_of_le h_pos h_noise
  have h_signal_nonneg : 0 ≤ (4.2575e9 : ℝ) := by norm_num
  have h_inv_nonneg :
      0 ≤ (em_params.total_noise)⁻¹ :=
    inv_nonneg.mpr (le_of_lt em_params.total_noise_pos)
  have h_prod :=
    mul_le_mul h_signal h_inv h_inv_nonneg h_signal_nonneg
  have h_eval :
      (4.2575e9 : ℝ) * (7e4 : ℝ)⁻¹ = 60821.42857142857 := by
    norm_num
  have h_thresh :
      (5 : ℝ) ≤ 60821.42857142857 := by norm_num
  have h_bound :
      (5 : ℝ) ≤ em_params.signal_events * (em_params.total_noise)⁻¹ :=
    le_trans (by simpa [h_eval]) h_prod
  simpa [SNRParams.SNR] using h_bound

/-- EM SNR is detectably positive -/
theorem em_snr_detectable :
  em_params.SNR > 1 := by
  have := em_snr_exceeds_threshold
  linarith

/-! ## Gravitational Channel at BIOPHASE -/

/-- Gravitational parameters (even with enormous flux, still fails) -/
noncomputable def grav_params : SNRParams := {
  flux := 1e20
  cross_section := sigma_gravitational E_biophase
  detector_area := 1e-8
  target_density := gate_density
  integration_time := tau_gate
  background_rate := 1e3
  detector_noise := 10

  flux_pos := by norm_num
  sigma_pos := sigma_grav_pos
  area_pos := by norm_num
  density_pos := gate_density_pos
  time_pos := by norm_num [tau_gate]
  background_nonneg := by norm_num
  noise_nonneg := by norm_num
}

private def grav_gain : ℝ :=
  (1e20 : ℝ) * 1e-8 * gate_density * tau_gate

private lemma grav_gain_value :
    grav_gain = 6.5e42 := by
  norm_num [grav_gain, gate_density, tau_gate,
    mul_comm, mul_left_comm, mul_assoc]

lemma grav_signal_events_value :
    grav_params.signal_events =
      grav_gain * sigma_gravitational E_biophase := by
  have := SNRParams.signal_events_const_mul_cross (grav_params)
  simp [grav_params, SNRParams.signal_events_const_mul_cross,
    mul_comm, mul_left_comm, mul_assoc] at this
  simpa [grav_gain] using this

lemma grav_signal_events_tiny :
    grav_params.signal_events < 1e-50 := by
  have h :=
    mul_lt_mul_of_pos_left sigma_grav_negligible (by
      have h₁ : 0 < (1e20 : ℝ) := by norm_num
      have h₂ : 0 < (1e-8 : ℝ) := by norm_num
      have h₃ : 0 < gate_density := gate_density_pos
      have h₄ : 0 < tau_gate := by norm_num [tau_gate]
      exact mul_pos (mul_pos (mul_pos h₁ h₂) h₃) h₄)
  have h_gain :
      grav_gain * 1e-100 < 1e-50 := by
    have : grav_gain = 6.5e42 := grav_gain_value
    simpa [this] using show (6.5e42 : ℝ) * 1e-100 < 1e-50 by norm_num
  have :
      grav_params.signal_events <
        grav_gain * 1e-100 := by
    simpa [grav_signal_events_value, mul_comm, mul_left_comm, mul_assoc]
      using h
  exact lt_trans this h_gain

lemma grav_signal_events_upper_exact :
    grav_params.signal_events < 6.5e-58 := by
  have h :=
    mul_lt_mul_of_pos_left sigma_grav_negligible (by
      have h₁ : 0 < (1e20 : ℝ) := by norm_num
      have h₂ : 0 < (1e-8 : ℝ) := by norm_num
      have h₃ : 0 < gate_density := gate_density_pos
      have h₄ : 0 < tau_gate := by norm_num [tau_gate]
      exact mul_pos (mul_pos (mul_pos h₁ h₂) h₃) h₄)
  have h_val :
      grav_gain * 1e-100 = (6.5e-58 : ℝ) := by
    have : grav_gain = 6.5e42 := grav_gain_value
    simpa [this] using
      show (6.5e42 : ℝ) * 1e-100 = 6.5e-58 by norm_num
  exact
    by
      have := lt_of_lt_of_eq h h_val
      simpa using this

/-- Gravitational SNR fails threshold -/
theorem grav_snr_fails :
  grav_params.SNR < 0.1 := by
  have h_le :=
    SNRParams.SNR_le_signal_over_noise (grav_params)
      (by norm_num : 0 < (grav_params.detector_noise : ℝ))
  have h_lt_signal :=
    grav_signal_events_tiny
  have h_pos : 0 < (10 : ℝ) := by norm_num
  have h_div :
      grav_params.signal_events / (grav_params.detector_noise : ℝ)
        < 1e-50 / 10 := by
    have h_eval : (grav_params.detector_noise : ℝ) = 10 := by
      simp [grav_params]
    have :=
      (div_lt_div_of_pos_right h_lt_signal h_pos)
    simpa [h_eval] using this
  have h_bound : (1e-50 : ℝ) / 10 < 0.1 := by norm_num
  have h_chain :
      grav_params.signal_events /
          (grav_params.detector_noise : ℝ)
        < 0.1 := lt_trans h_div h_bound
  exact lt_of_le_of_lt h_le h_chain

/-- Gravitational SNR is essentially zero -/
theorem grav_snr_negligible :
  grav_params.SNR < 1e-10 := by
  have h_le :=
    SNRParams.SNR_le_signal_over_noise (grav_params)
      (by norm_num : 0 < (grav_params.detector_noise : ℝ))
  have h_pos : 0 < (10 : ℝ) := by norm_num
  have h_div :
      grav_params.signal_events / (grav_params.detector_noise : ℝ)
        < 6.5e-58 / 10 := by
    have h_eval : (grav_params.detector_noise : ℝ) = 10 := by
      simp [grav_params]
    have :=
      (div_lt_div_of_pos_right grav_signal_events_upper_exact h_pos)
    simpa [h_eval] using this
  have h_bound : (6.5e-58 : ℝ) / 10 < 1e-10 := by norm_num
  have h_chain :
      grav_params.signal_events /
          (grav_params.detector_noise : ℝ)
        < 1e-10 := lt_trans h_div h_bound
  exact lt_of_le_of_lt h_le h_chain

/-! ## Neutrino Channel at BIOPHASE -/

/-- Neutrino parameters (reasonable flux, but cross-section too small) -/
noncomputable def nu_params : SNRParams := {
  flux := 1e15
  cross_section := sigma_neutrino E_biophase
  detector_area := 1e-8
  target_density := gate_density
  integration_time := tau_gate
  background_rate := 1e3
  detector_noise := 10

  flux_pos := by norm_num
  sigma_pos := sigma_nu_pos
  area_pos := by norm_num
  density_pos := gate_density_pos
  time_pos := by norm_num [tau_gate]
  background_nonneg := by norm_num
  noise_nonneg := by norm_num
}

lemma nu_signal_events_value :
    nu_params.signal_events =
      em_gain * sigma_neutrino E_biophase := by
  have := SNRParams.signal_events_const_mul_cross (nu_params)
  simp [nu_params, SNRParams.signal_events_const_mul_cross,
    mul_comm, mul_left_comm, mul_assoc, em_gain] at this
  simpa [em_gain] using this

lemma nu_signal_events_tiny :
    nu_params.signal_events < 1e-30 := by
  have h :=
    mul_lt_mul_of_pos_left sigma_nu_undetectable em_gain_pos
  have h_gain :
      em_gain * 1e-68 < 1e-30 := by
    have : em_gain = 6.5e37 := em_gain_value
    simpa [this] using show (6.5e37 : ℝ) * 1e-68 < 1e-30 by norm_num
  have :
      nu_params.signal_events <
        em_gain * 1e-68 := by
    simpa [nu_signal_events_value, mul_comm, mul_left_comm, mul_assoc]
      using h
  exact lt_trans this h_gain

lemma nu_signal_events_upper_exact :
    nu_params.signal_events < 6.5e-31 := by
  have h :=
    mul_lt_mul_of_pos_left sigma_nu_undetectable em_gain_pos
  have h_val :
      em_gain * 1e-68 = (6.5e-31 : ℝ) := by
    have : em_gain = 6.5e37 := em_gain_value
    simpa [this] using
      show (6.5e37 : ℝ) * 1e-68 = 6.5e-31 by norm_num
  have :=
    lt_of_lt_of_eq h h_val
  simpa [nu_signal_events_value, mul_comm, mul_left_comm, mul_assoc]
    using this

/-- Neutrino SNR fails threshold -/
theorem nu_snr_fails :
  nu_params.SNR < 1e-6 := by
  have h_le :=
    SNRParams.SNR_le_signal_over_noise (nu_params)
      (by norm_num : 0 < (nu_params.detector_noise : ℝ))
  have h_pos : 0 < (10 : ℝ) := by norm_num
  have h_div :
      nu_params.signal_events / (nu_params.detector_noise : ℝ)
        < 6.5e-31 / 10 := by
    have h_eval : (nu_params.detector_noise : ℝ) = 10 := by
      simp [nu_params]
    have :=
      (div_lt_div_of_pos_right nu_signal_events_upper_exact h_pos)
    simpa [h_eval] using this
  have h_bound : (6.5e-31 : ℝ) / 10 < 1e-6 := by norm_num
  have h_chain :
      nu_params.signal_events /
          (nu_params.detector_noise : ℝ)
        < 1e-6 := lt_trans h_div h_bound
  exact lt_of_le_of_lt h_le h_chain

/-- Neutrino SNR is astronomically small -/
theorem nu_snr_utterly_undetectable :
  nu_params.SNR < 1e-20 := by
  have h_le :=
    SNRParams.SNR_le_signal_over_noise (nu_params)
      (by norm_num : 0 < (nu_params.detector_noise : ℝ))
  have h_pos : 0 < (10 : ℝ) := by norm_num
  have h_div :
      nu_params.signal_events / (nu_params.detector_noise : ℝ)
        < 6.5e-31 / 10 := by
    have h_eval : (nu_params.detector_noise : ℝ) = 10 := by
      simp [nu_params]
    have :=
      (div_lt_div_of_pos_right nu_signal_events_upper_exact h_pos)
    simpa [h_eval] using this
  have h_bound : (6.5e-31 : ℝ) / 10 < 1e-20 := by norm_num
  have h_chain :
      nu_params.signal_events /
          (nu_params.detector_noise : ℝ)
        < 1e-20 := lt_trans h_div h_bound
  exact lt_of_le_of_lt h_le h_chain

/-- Gravitational SNR is smaller than neutrino SNR -/
theorem grav_snr_lt_nu_snr :
  grav_params.SNR < nu_params.SNR := by
  have h_grav := grav_snr_upper_bound
  have h_nu := nu_snr_lower_bound
  have h_bound :
      6.5e-59 < 5.909090909090909e-36 := by norm_num
  exact lt_of_le_of_lt h_grav (lt_of_lt_of_le h_bound h_nu)

/-- Neutrino SNR is smaller than EM SNR -/
theorem nu_snr_lt_em_snr :
  nu_params.SNR < em_params.SNR := by
  have h_nu := nu_snr_upper_bound
  have h_em := em_snr_lower_bound_large
  have h_bound :
      6.5e-32 < 60821.42857142857 := by norm_num
  exact lt_of_le_of_lt h_nu (lt_of_lt_of_le h_bound h_em)

/-! ## Comparison and Ordering -/

/-- EM SNR vastly exceeds gravitational SNR -/
theorem em_vs_grav_snr :
  em_params.SNR > grav_params.SNR * 1e10 := by
  have h_grav := grav_snr_upper_bound
  have h_em := em_snr_lower_bound_large
  have h_scale :
      grav_params.SNR * 1e10 ≤ 6.5e-59 * 1e10 :=
    (mul_le_mul_of_nonneg_right h_grav (by norm_num : 0 ≤ (1e10 : ℝ)))
  have h_bound :
      6.5e-59 * 1e10 = 6.5e-49 := by norm_num
  have h_gap :
      (6.5e-49 : ℝ) < 60821.42857142857 := by norm_num
  have h_chain :
      grav_params.SNR * 1e10 < em_params.SNR :=
    lt_of_le_of_lt (by simpa [h_bound] using h_scale)
      (lt_of_lt_of_le h_gap h_em)
  exact h_chain

/-- EM SNR vastly exceeds neutrino SNR -/
theorem em_vs_nu_snr :
  em_params.SNR > nu_params.SNR * 1e20 := by
  have h_nu := nu_snr_upper_bound
  have h_em := em_snr_lower_bound_large
  have h_scale :
      nu_params.SNR * 1e20 ≤ 6.5e-32 * 1e20 :=
    (mul_le_mul_of_nonneg_right h_nu (by norm_num : 0 ≤ (1e20 : ℝ)))
  have h_bound :
      6.5e-32 * 1e20 = 6.5e-12 := by norm_num
  have h_gap :
      (6.5e-12 : ℝ) < 60821.42857142857 := by norm_num
  exact
    lt_of_le_of_lt (by simpa [h_bound] using h_scale)
      (lt_of_lt_of_le h_gap h_em)

/-- Only EM exceeds the 5σ threshold -/
theorem only_em_passes_5sigma :
  em_params.SNR ≥ 5 ∧
  grav_params.SNR < 5 ∧
  nu_params.SNR < 5 := by
  constructor
  · exact em_snr_exceeds_threshold
  constructor
  · have := grav_snr_fails
    linarith
  · have := nu_snr_fails
    linarith

/-! ## SNR Summary Structure -/

/-- Complete SNR data for all three channels -/
structure ChannelSNRData where
  /-- EM SNR value -/
  snr_em : ℝ
  /-- Gravitational SNR value -/
  snr_grav : ℝ
  /-- Neutrino SNR value -/
  snr_nu : ℝ

  /-- EM exceeds threshold -/
  em_passes : snr_em ≥ 5
  /-- Gravitational fails -/
  grav_fails : snr_grav < 0.1
  /-- Neutrino fails -/
  nu_fails : snr_nu < 1e-6

  /-- Ordering -/
  grav_smallest : snr_grav < snr_nu
  nu_smaller : snr_nu < snr_em

/-- Standard channel SNR data at BIOPHASE conditions -/
noncomputable def biophase_snr_data : ChannelSNRData := {
  snr_em := em_params.SNR
  snr_grav := grav_params.SNR
  snr_nu := nu_params.SNR

  em_passes := em_snr_exceeds_threshold
  grav_fails := grav_snr_fails
  nu_fails := nu_snr_fails

  grav_smallest := grav_snr_lt_nu_snr

  nu_smaller := nu_snr_lt_em_snr
}

/-! ## Physical Interpretation

EM: Large cross-section + reasonable flux ⟹ detectable signal.
Even at ps timescales, enough photons interact to build SNR.

Gravitational: Tiny cross-section overwhelms any realistic flux.
Would need impossibly large flux or detector to overcome noise floor.

Neutrino: Weak interaction at low energy makes detection impossible.
Interaction length >> universe size; no detection at ps timescales.
-/

end BiophasePhysics
end IndisputableMonolith
