import Mathlib

namespace IndisputableMonolith
namespace Constants

/-- The fundamental RS time quantum (RS-native). τ₀ = 1 tick. -/
@[simp] def tick : ℝ := 1

/-- Notation for fundamental tick. -/
abbrev τ₀ : ℝ := tick

/-- One octave = 8 ticks: the fundamental evolution period. -/
def octave : ℝ := 8 * tick

/-- Golden ratio φ as a concrete real. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  -- Use that √5 > 0
  have hroot_pos : 0 < Real.sqrt 5 := by
    have : (0 : ℝ) < 5 := by norm_num
    exact Real.sqrt_pos.mpr this
  have hnum_pos : 0 < 1 + Real.sqrt 5 := by exact add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt hroot_pos)
  simpa [phi] using (div_pos hnum_pos htwo)

lemma one_lt_phi : 1 < phi := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hsqrt_gt : Real.sqrt 1 < Real.sqrt 5 := by
    simpa [Real.sqrt_one] using (Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5))
  have h2lt : (2 : ℝ) < 1 + Real.sqrt 5 := by
    have h1lt : (1 : ℝ) < Real.sqrt 5 := by simpa [Real.sqrt_one] using hsqrt_gt
    linarith
  have hdiv : (2 : ℝ) / 2 < (1 + Real.sqrt 5) / 2 := (div_lt_div_of_pos_right h2lt htwo)
  have hone_lt : 1 < (1 + Real.sqrt 5) / 2 := by simpa using hdiv
  simpa [phi] using hone_lt

lemma phi_ge_one : 1 ≤ phi := le_of_lt one_lt_phi
lemma phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos
lemma phi_ne_one : phi ≠ 1 := ne_of_gt one_lt_phi

lemma phi_lt_two : phi < 2 := by
  have hsqrt5_lt : Real.sqrt 5 < 3 := by
    have h5_lt_9 : (5 : ℝ) < 9 := by norm_num
    have h9_eq : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)]
    have : Real.sqrt 5 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) h5_lt_9
    rwa [h9_eq] at this
  have hnum_lt : 1 + Real.sqrt 5 < 4 := by linarith
  have : (1 + Real.sqrt 5) / 2 < 4 / 2 := div_lt_div_of_pos_right hnum_lt (by norm_num)
  simp only [phi]
  linarith

/-! ### φ irrationality -/

/-- φ is irrational (degree 2 algebraic, not rational).

    Proof: Our φ equals Mathlib's golden ratio, which is proven irrational
    via the irrationality of √5 (5 is prime, hence not a perfect square). -/
theorem phi_irrational : Irrational phi := by
  -- Our phi equals Mathlib's goldenRatio
  have h_eq : phi = Real.goldenRatio := rfl
  rw [h_eq]
  exact Real.goldenRatio_irrational

/-! ### φ power bounds -/

/-- Key identity: φ² = φ + 1 (from the defining equation x² - x - 1 = 0). -/
lemma phi_sq_eq : phi^2 = phi + 1 := by
  simp only [phi]
  have h5_pos : (0 : ℝ) ≤ 5 := by norm_num
  have hsq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt h5_pos
  ring_nf
  linear_combination (1/4) * hsq

/-- Tighter lower bound: φ > 1.5 (since √5 > 2, so (1 + √5)/2 > 1.5). -/
lemma phi_gt_onePointFive : (1.5 : ℝ) < phi := by
  simp only [phi]
  have h5 : (2 : ℝ) < Real.sqrt 5 := by
    have h : (2 : ℝ)^2 < 5 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_lt_sqrt (by norm_num) h
  linarith

/-- Tighter upper bound: φ < 1.62 (since √5 < 2.24). -/
lemma phi_lt_onePointSixTwo : phi < (1.62 : ℝ) := by
  simp only [phi]
  have h5 : Real.sqrt 5 < (2.24 : ℝ) := by
    have h : (5 : ℝ) < (2.24 : ℝ)^2 := by norm_num
    have h24_pos : (0 : ℝ) ≤ 2.24 := by norm_num
    rw [← Real.sqrt_sq h24_pos]
    exact Real.sqrt_lt_sqrt (by norm_num) h
  linarith

/-- φ² is between 2.5 and 2.7.
    φ² = φ + 1 ≈ 2.618 (exact: (3 + √5)/2). -/
lemma phi_squared_bounds : (2.5 : ℝ) < phi^2 ∧ phi^2 < 2.7 := by
  rw [phi_sq_eq]
  have h1 := phi_gt_onePointFive
  have h2 := phi_lt_onePointSixTwo
  constructor <;> linarith

/-- φ³ is between 4.0 and 4.25.
    φ³ = φ² + φ = 2φ + 1 ≈ 4.236. -/
lemma phi_cubed_bounds : (4.0 : ℝ) < phi^3 ∧ phi^3 < 4.25 := by
  -- φ³ = φ × φ² = φ(φ + 1) = φ² + φ = (φ + 1) + φ = 2φ + 1
  have h_phi_cu : phi^3 = 2 * phi + 1 := by
    calc phi^3 = phi * phi^2 := by ring
      _ = phi * (phi + 1) := by rw [phi_sq_eq]
      _ = phi^2 + phi := by ring
      _ = (phi + 1) + phi := by rw [phi_sq_eq]
      _ = 2 * phi + 1 := by ring
  rw [h_phi_cu]
  have h1 := phi_gt_onePointFive
  have h2 := phi_lt_onePointSixTwo
  constructor <;> linarith

/-- φ⁴ is between 6.5 and 6.9.
    φ⁴ = φ³ + φ² = 3φ + 2 ≈ 6.854. -/
lemma phi_fourth_bounds : (6.5 : ℝ) < phi^4 ∧ phi^4 < 6.9 := by
  -- φ⁴ = φ² × φ² = (φ + 1)² = φ² + 2φ + 1 = (φ + 1) + 2φ + 1 = 3φ + 2
  have h_phi_fo : phi^4 = 3 * phi + 2 := by
    calc phi^4 = (phi^2)^2 := by ring
      _ = (phi + 1)^2 := by rw [phi_sq_eq]
      _ = phi^2 + 2 * phi + 1 := by ring
      _ = (phi + 1) + 2 * phi + 1 := by rw [phi_sq_eq]
      _ = 3 * phi + 2 := by ring
  rw [h_phi_fo]
  have h1 := phi_gt_onePointFive
  have h2 := phi_lt_onePointSixTwo
  constructor <;> linarith

/-! ### Canonical constants derived from φ -/

/-- Canonical locked fine-structure constant: α_lock = (1 − 1/φ)/2. -/
@[simp] noncomputable def alphaLock : ℝ := (1 - 1 / phi) / 2

lemma alphaLock_pos : 0 < alphaLock := by
  have hphi := one_lt_phi
  unfold alphaLock
  have : 1 / phi < 1 := (div_lt_one phi_pos).mpr hphi
  linarith

lemma alphaLock_lt_one : alphaLock < 1 := by
  have hpos : 0 < phi := phi_pos
  unfold alphaLock
  have : 1 / phi > 0 := one_div_pos.mpr hpos
  linarith

/-- Canonical locked C_lag constant: C_lock = φ^{−5}. -/
@[simp] noncomputable def cLagLock : ℝ := phi ^ (-(5 : ℝ))

lemma cLagLock_pos : 0 < cLagLock := by
  have hphi : 0 < phi := phi_pos
  unfold cLagLock
  exact Real.rpow_pos_of_pos hphi (-(5 : ℝ))

/-- The elementary ledger bit cost J_bit = ln φ. -/
noncomputable def J_bit : ℝ := Real.log phi

/-- Coherence energy in RS units (dimensionless).
    By Phase 2 derivation, E_coh = C_lock = φ⁻⁵. -/
noncomputable def E_coh : ℝ := cLagLock

lemma E_coh_pos : 0 < E_coh := cLagLock_pos

/-! ### RS-native fundamental units (parameter-free)

The **core theory** is expressed in RS-native units:

- `tau0 = 1` tick (time quantum)
- `ell0 = 1` voxel (length quantum)
- `c = 1` voxel/tick

All SI/CODATA anchoring is treated as **external calibration** and lives in
separate modules (e.g. `IndisputableMonolith.Constants.Consistency`,
`IndisputableMonolith.Constants.Derivation`, `IndisputableMonolith.Constants.Codata`,
and `IndisputableMonolith.Constants.RSNativeUnits`). -/

/-- The fundamental time unit τ₀ (duration of one tick) in RS-native units. -/
@[simp] noncomputable def tau0 : ℝ := tick

lemma tau0_pos : 0 < tau0 := by
  simp [tau0, tick]

/-- Reduced Planck constant ħ in RS-native units: ħ = E_coh · τ₀ = φ⁻⁵ · 1. -/
noncomputable def hbar : ℝ := cLagLock * tau0

lemma hbar_pos : 0 < hbar := mul_pos cLagLock_pos tau0_pos

/-- The speed of light c in RS-native units (voxel/tick). -/
@[simp] noncomputable def c : ℝ := 1

lemma c_pos : 0 < c := by
  simp [c]

/-- The fundamental length unit ℓ₀ in RS-native units (voxel). -/
@[simp] noncomputable def ell0 : ℝ := 1

lemma ell0_pos : 0 < ell0 := by
  simp [ell0]

/-- Light-cone identity: ℓ₀ = c · τ₀ (in RS-native units). -/
lemma c_ell0_tau0 : c * tau0 = ell0 := by
  simp [c, tau0, ell0, tick]

/-- Fundamental recognition wavelength λ_rec.
    In the 8-tick cycle, λ_rec = ℓ₀ (in RS-native units). -/
noncomputable def lambda_rec : ℝ := ell0

lemma lambda_rec_pos : 0 < lambda_rec := by
  simpa [lambda_rec] using ell0_pos

/-- Newton's gravitational constant G derived from first principles (RS-native form).
    \(G = \lambda_{\text{rec}}^2 c^3 / (\pi \hbar)\). -/
noncomputable def G : ℝ := (lambda_rec^2) * (c^3) / (Real.pi * hbar)

lemma G_pos : 0 < G := by
  unfold G
  apply div_pos
  · apply mul_pos
    · exact pow_pos lambda_rec_pos 2
    · exact pow_pos c_pos 3
  · apply mul_pos
    · exact Real.pi_pos
    · exact hbar_pos

/-!
  ## CODATA / SI constants (quarantined)

  The empirical SI/CODATA numeric constants live in
  `IndisputableMonolith/Constants/Codata.lean` and are intentionally **excluded**
  from the certified surface import-closure.

  If you need them for numeric comparisons or empirical reports, import
  `IndisputableMonolith.Constants.Codata` explicitly.
-/

/-- Minimal RS units used in Core. -/
structure RSUnits where
  tau0 : ℝ
  ell0 : ℝ
  c    : ℝ
  c_ell0_tau0 : c * tau0 = ell0

/-- Dimensionless bridge ratio \(K\).

Defined (non-circularly) as \(K = \varphi^{1/2}\). -/
@[simp] noncomputable def K : ℝ := phi ^ (1/2 : ℝ)

@[simp] lemma K_def : K = phi ^ (1/2 : ℝ) := rfl

lemma K_pos : 0 < K := by
  -- φ > 0, hence φ^(1/2) > 0
  simpa [K] using Real.rpow_pos_of_pos phi_pos (1/2 : ℝ)

lemma K_nonneg : 0 ≤ K := le_of_lt K_pos

end Constants
end IndisputableMonolith
