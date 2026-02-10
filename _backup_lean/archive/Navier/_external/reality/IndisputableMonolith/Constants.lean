import Mathlib

namespace IndisputableMonolith
namespace Constants

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

/-- Canonical locked C_lag constant: C_lock = φ^{−5}. -/
@[simp] noncomputable def cLagLock : ℝ := phi ^ (-(5 : ℝ))

lemma alphaLock_pos : 0 < alphaLock := by
  have hφ : 0 < phi := phi_pos
  have hφ_gt : 1 < phi := one_lt_phi
  have hsub : 0 < 1 - 1 / phi := by
    have hlt : 1 / phi < 1 := by
      rw [div_lt_one hφ]
      exact hφ_gt
    exact sub_pos.mpr hlt
  have htwo : 0 < (2 : ℝ) := by norm_num
  unfold alphaLock
  exact div_pos hsub htwo

lemma alphaLock_lt_one : alphaLock < 1 := by
  have hφ : 1 < phi := one_lt_phi
  -- (1 - 1/φ)/2 < 1 ↔ 1 - 1/φ < 2 ↔ -1/φ < 1 ↔ 1/φ > -1 (trivial).
  have hden : 0 < (2 : ℝ) := by norm_num
  have hnum : 1 - 1 / phi < 2 := by
    have hinv_pos : 0 < 1 / phi := div_pos (by norm_num) phi_pos
    have hinv_nonneg : 0 ≤ 1 / phi := le_of_lt hinv_pos
    have h1 : -(1 / phi) ≤ 0 := neg_nonpos.mpr hinv_nonneg
    have h2 : -(1 / phi) < 1 := lt_of_le_of_lt h1 (by norm_num)
    calc
      1 - 1 / phi = 1 + (-(1 / phi)) := by ring
      _ < 1 + 1 := by linarith
      _ = 2 := by norm_num
  have : (1 - 1 / phi) / 2 < (2 : ℝ) / 2 := (div_lt_div_of_pos_right hnum hden)
  unfold alphaLock
  calc
    (1 - 1 / phi) / 2 < (2 : ℝ) / 2 := this
    _ = 1 := by norm_num

lemma cLagLock_pos : 0 < cLagLock := by
  have hphi : 0 < phi := phi_pos
  unfold cLagLock
  exact Real.rpow_pos_of_pos hphi (-(5 : ℝ))

/-
  Physical constants used throughout the Light Language proofs.  We keep
  conservative placeholder values (all equal to 1 in SI units) to avoid dragging
  in numerical dependencies; only positivity matters for the gate arguments.
-/
@[simp] noncomputable def hbar : ℝ := 1
@[simp] noncomputable def G : ℝ := 1
@[simp] noncomputable def c : ℝ := 1

lemma hbar_pos : 0 < hbar := by simpa [hbar]
lemma G_pos : 0 < G := by simpa [G]
lemma c_pos : 0 < c := by simpa [c]

/-- Minimal RS units used in Core. -/
structure RSUnits where
  tau0 : ℝ
  ell0 : ℝ
  c    : ℝ
  c_ell0_tau0 : c * tau0 = ell0

/-- Minimal global constant K placeholder. -/
@[simp] def K : ℝ := 1

lemma K_pos : 0 < K := by simp [K]
lemma K_nonneg : 0 ≤ K := by simp [K]

end Constants
end IndisputableMonolith
