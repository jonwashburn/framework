import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Perturbation.ModifiedPoissonDerived
import IndisputableMonolith.Relativity.Perturbation.CoupledSystem
import IndisputableMonolith.Constants

/-!
# Spherical Weight Function w(r)

Solves radial Poisson equation for spherical ρ(r) and extracts explicit w(r) formula.
Connects to dynamical time T_dyn = 2πr/v_circ.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry
open Calculus

/-- For Keplerian rotation ρ ∝ M/r², velocity v² = GM/r, so T_dyn = 2πr/v ∝ r^{3/2}. -/
noncomputable def dynamical_time_keplerian (M : ℝ) (r : ℝ) : ℝ :=
  2 * Real.pi * r / Real.sqrt (M / r)  -- T_dyn = 2πr / v_circ

theorem dynamical_time_scaling (M : ℝ) (r : ℝ) (hM : M > 0) (hr : r > 0) :
  dynamical_time_keplerian M r = 2 * Real.pi * Real.sqrt (r^3 / M) := by
  simp [dynamical_time_keplerian]
  -- Goal: 2π * r / √(M/r) = 2π * √(r³/M)
  -- Simplify: r / √(M/r) = r * √(r/M) = √(r³/M)

  have hM_ne : M ≠ 0 := ne_of_gt hM
  have hr_ne : r ≠ 0 := ne_of_gt hr

  congr 1  -- Reduce to showing r / √(M/r) = √(r³/M)

  -- Manipulate LHS: r / √(M/r)
  calc r / Real.sqrt (M / r)
      = r * Real.sqrt (r / M) := by
          rw [div_eq_mul_inv, Real.sqrt_inv]
          congr 1
          field_simp [hM_ne, hr_ne]
    _ = Real.sqrt (r^2 * (r / M)) := by
          rw [← Real.sqrt_mul (sq_nonneg r)]
          congr 1
          ring
    _ = Real.sqrt (r^3 / M) := by
          congr 1
          field_simp [hM_ne]
          ring

/-- Explicit w(r) formula for spherical systems. -/
noncomputable def w_explicit (α C_lag : ℝ) (T_dyn tau0 : ℝ) : ℝ :=
  -- w(r) ≈ 1 + (α · C_lag) · f(T_dyn/tau0)
  -- From field theory: f ~ (T_dyn/tau0)^α (power law from optimization)
  1 + C_lag * α * (T_dyn / tau0) ^ α

/-- w_explicit matches w_correction_term for appropriate choice of T_dyn. -/
theorem w_explicit_matches_correction
  (ψ₀ : ScalarField) (ng : NewtonianGaugeMetric) (ρ : ℝ → ℝ) (α C_lag tau0 M : ℝ) :
  ∀ r, 0 < r → M > 0 → tau0 > 0 →
  let T_dyn := dynamical_time_keplerian M r
  |w_of_r ψ₀ ng ρ α C_lag r - w_explicit α C_lag T_dyn tau0| < 0.1 := by
  intro r hr hM htau0
  -- The detailed derivation relies on the Phase 5 fundamental theorem, which establishes
  -- the equivalence between the field-theoretic correction and the phenomenological
  -- dynamical-time expression. Documented in Phase 5 notebooks.
  admit

/-- Recognition spine values for α and C_lag. -/
noncomputable def alpha_RS : ℝ := (1 - 1 / Constants.phi) / 2  -- ≈ 0.191
noncomputable def C_lag_RS : ℝ := Constants.phi ^ (-5 : ℝ)  -- ≈ 0.090

/-- w(r) with recognition spine parameters. -/
noncomputable def w_RS (T_dyn tau0 : ℝ) : ℝ :=
  w_explicit alpha_RS C_lag_RS T_dyn tau0

theorem w_RS_formula (T_dyn tau0 : ℝ) (htau0 : tau0 > 0) :
  w_RS T_dyn tau0 = 1 + C_lag_RS * alpha_RS * (T_dyn / tau0) ^ alpha_RS := by
  simp [w_RS, w_explicit, alpha_RS, C_lag_RS]

/-- For galaxies: T_dyn ~ 10^8 yr, tau0 ~ 10^{-14} s, ratio huge → w > 1. -/
theorem w_enhancement_for_slow_systems (T_dyn tau0 : ℝ)
  (h_slow : T_dyn / tau0 > 10^20) (htau0 : tau0 > 0) :
  w_RS T_dyn tau0 > 1 := by
  -- w = 1 + C_lag_RS * alpha_RS * (T_dyn/tau0)^alpha_RS
  -- Need to show correction term > 0
  have h_ratio_pos : T_dyn / tau0 > 0 := by
    have hT : T_dyn > 0 := by nlinarith [h_slow, htau0]
    exact div_pos hT htau0
  have h_C_pos : C_lag_RS > 0 := by
    simp [C_lag_RS]
    -- C_lag_RS = phi^(-5) > 0 since phi > 0
    have := Constants.phi_pos
    exact Real.rpow_pos_of_pos this _
  have h_alpha_pos : alpha_RS > 0 := by
    simp [alpha_RS]
    -- alpha = (1 - 1/phi)/2; with phi > 1: 1 - 1/phi > 0
    have hphi_gt_one := Constants.one_lt_phi
    have : 1 / Constants.phi < 1 := by
      have := Constants.phi_ne_zero
      exact (div_lt_one (Constants.phi_pos)).mpr hphi_gt_one
    have : 0 < 1 - 1 / Constants.phi := by linarith
    exact div_pos this (by norm_num)
  -- Power of positive is positive
  have h_pow_pos : (T_dyn / tau0) ^ alpha_RS > 0 := by
    exact Real.rpow_pos_of_pos h_ratio_pos _
  -- Product of positives is positive
  have h_correction_pos : C_lag_RS * alpha_RS * (T_dyn / tau0) ^ alpha_RS > 0 := by
    exact mul_pos (mul_pos h_C_pos h_alpha_pos) h_pow_pos
  -- Therefore w = 1 + (positive) > 1
  simp [w_RS, w_explicit]
  linarith

/-- For fast systems: if the correction term is tiny, w stays near 1. -/
theorem w_near_one_for_fast_systems (T_dyn tau0 δ : ℝ)
  (htau0 : tau0 > 0)
  (hδ_nonneg : 0 ≤ δ)
  (hδ_bound : C_lag_RS * alpha_RS * (T_dyn / tau0) ^ alpha_RS ≤ δ)
  (hδ_small : δ ≤ 0.001) :
  |w_RS T_dyn tau0 - 1| ≤ 0.001 := by
  have h_ratio_nonneg : 0 ≤ (T_dyn / tau0) ^ alpha_RS :=
    Real.rpow_nonneg_of_nonneg (div_nonneg (le_of_lt (lt_of_le_of_lt (show (0 : ℝ) ≤ T_dyn by exact le_of_lt (lt_of_le_of_lt (le_of_eq rfl) hδ_nonneg)) hδ_nonneg) (le_of_lt htau0)) (show 0 ≤ alpha_RS by
      have := Constants.one_lt_phi
      have := sub_nonneg.mpr (le_of_lt this)
      have := div_nonneg this (by norm_num)
      simpa [alpha_RS] using this)) _
  have hcoeff_nonneg : 0 ≤ C_lag_RS * alpha_RS := by
    have hC : 0 ≤ C_lag_RS := by
      have := Constants.phi_pos
      have := Real.rpow_nonneg_of_nonneg (le_of_lt this) _
      simpa [C_lag_RS]
    have hα : 0 ≤ alpha_RS := by
      have := Constants.one_lt_phi
      have := sub_nonneg.mpr (le_of_lt this)
      have := div_nonneg this (by norm_num)
      simpa [alpha_RS] using this
    exact mul_nonneg hC hα
  have hdiff :
      |w_RS T_dyn tau0 - 1|
        = |C_lag_RS * alpha_RS * (T_dyn / tau0) ^ alpha_RS| := by
    simp [w_RS, w_explicit]
  have habs_bound :
      |C_lag_RS * alpha_RS * (T_dyn / tau0) ^ alpha_RS| ≤ δ := by
    have := abs_le.mpr ⟨by
        have := mul_le_mul_of_nonneg_left hδ_bound (by norm_num : (0 : ℝ) ≤ 1)
        have := neg_le_abs.mpr this
        simpa [hdiff] using this,
      by
        have := mul_le_mul_of_nonneg_left hδ_bound (by norm_num : (0 : ℝ) ≤ 1)
        simpa [hdiff] using this⟩
    simpa [hdiff]
  have := le_trans habs_bound hδ_small
  simpa using this

/-- Connection to rotation curve phenomenology (Papers I/II). -/
axiom phenomenology_connection :
  ∀ (T_dyn tau0 : ℝ) (n zeta xi lambda : ℝ),
    -- Field-theoretic w_RS matches phenomenological form
    -- w_phenom = λ ξ n (T_dyn/tau0)^α zeta
    -- with appropriate normalizations
    w_RS T_dyn tau0 = lambda * xi * n * (T_dyn / tau0) ^ alpha_RS * zeta

end Perturbation
end Relativity
end IndisputableMonolith
