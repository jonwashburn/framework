import Mathlib
import IndisputableMonolith.Relativity/ILG/Action
import IndisputableMonolith.Relativity/ILG/PPNDerive

open scoped Real

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Historical scaffold: potential Φ extracted from ψ backreaction. Retained for
    compatibility with higher-level certificates; currently treated as the
    `cLag` parameter. -/
noncomputable def Phi (ψ : RefreshField) (p : ILGParams) : ℝ := p.cLag

/-- Historical scaffold: potential Ψ extracted from ψ backreaction. Retained for
    compatibility with higher-level certificates; currently treated as the
    `alpha` parameter. -/
noncomputable def Psi (ψ : RefreshField) (p : ILGParams) : ℝ := p.alpha

/-- Baseline GR proxy Φ+Ψ, preserved to support existing reports. -/
noncomputable def baseline_potential (Φ Ψ : ℝ) : ℝ := Φ + Ψ

/-- Legacy lensing proxy built from Φ and Ψ. Wrapped over the new
    `lensing_strength` for downstream consistency. -/
noncomputable def lensing_proxy (ψ : RefreshField) (p : ILGParams) : ℝ :=
  baseline_potential (Phi ψ p) (Psi ψ p)

/-- Dimensionless lensing strength: `(1 + γ)/2` with γ from the ILG PPN expansion. -/
noncomputable def lensing_strength (ψ : RefreshField) (p : ILGParams) : ℝ :=
  (PPN.gamma_nl ψ p + 1) / 2

/-- GR reference value: lensing strength equals 1. -/
@[simp] def gr_lensing_strength : ℝ := 1

/-- Simple deflection integral along affine parameter s in a toy 1D model.
    Uses constant potentials here as a scaffold: α_hat ∝ ∫ d/dx (Φ+Ψ) ds,
    which reduces to a constant multiple when Φ, Ψ are constant in this toy model. -/
noncomputable def deflection (ψ : RefreshField) (p : ILGParams) (ℓ : ℝ) : ℝ :=
  lensing_strength ψ p * ℓ

/-- GR reference deflection for the same path. -/
@[simp] def deflection_GR (ℓ : ℝ) : ℝ := gr_lensing_strength * ℓ

/-- Time-delay uses the same strength factor at this order. -/
noncomputable def time_delay (ψ : RefreshField) (p : ILGParams) (ℓ : ℝ) : ℝ :=
  lensing_strength ψ p * ℓ

/-- GR reference time delay. -/
@[simp] def time_delay_GR (ℓ : ℝ) : ℝ := gr_lensing_strength * ℓ

/-- Dimensionless shear coefficient: deviation of lensing strength from the GR value. -/
noncomputable def shear_coeff (ψ : RefreshField) (p : ILGParams) : ℝ :=
  lensing_strength ψ p - 1

@[simp] theorem deflection_zero_path (ψ : RefreshField) (p : ILGParams) :
  deflection ψ p 0 = 0 := by
  simp [deflection]

@[simp] theorem time_delay_zero_path (ψ : RefreshField) (p : ILGParams) :
  time_delay ψ p 0 = 0 := by
  simp [time_delay]

lemma lensing_strength_diff (ψ : RefreshField) (p : ILGParams) :
    lensing_strength ψ p - 1
      = (PPN.gamma_nl ψ p - 1) * (1 / 2 : ℝ) := by
  unfold lensing_strength
  have :
      (PPN.gamma_nl ψ p + 1) * (1 / 2 : ℝ) - 1
        = (PPN.gamma_nl ψ p - 1) * (1 / 2 : ℝ) := by
    ring
  simpa [div_eq_mul_inv]

/-- Absolute deviation of the lensing strength from the GR value. -/
theorem lensing_strength_bound (ψ : RefreshField) (p : ILGParams) :
    |lensing_strength ψ p - 1|
      ≤ (1 / 20 : ℝ) * |p.cLag * p.alpha|
        + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|) := by
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have habs :
      |lensing_strength ψ p - 1|
        = (1 / 2 : ℝ) * |PPN.gamma_nl ψ p - 1| := by
    simpa [lensing_strength_diff ψ p, abs_mul, abs_of_nonneg hhalf, mul_comm, mul_left_comm,
      mul_assoc]
  have hγ := IndisputableMonolith.Relativity.ILG.gamma_nl_bound ψ p
  have hineq :
      (1 / 2 : ℝ) * |PPN.gamma_nl ψ p - 1|
        ≤ (1 / 2 : ℝ)
            * ((1 / 10 : ℝ) * |p.cLag * p.alpha|
                + (1 / 100 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)) := by
    exact mul_le_mul_of_nonneg_left hγ hhalf
  have hring :
      (1 / 2 : ℝ)
          * ((1 / 10 : ℝ) * |p.cLag * p.alpha|
              + (1 / 100 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|))
        = (1 / 20 : ℝ) * |p.cLag * p.alpha|
            + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|) := by
    ring
  have step₁ : |lensing_strength ψ p - 1|
      ≤ (1 / 2 : ℝ)
          * ((1 / 10 : ℝ) * |p.cLag * p.alpha|
              + (1 / 100 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)) :=
    by simpa [habs] using hineq
  simpa [hring]

/-- Absolute deviation of the deflection coefficient from GR. -/
theorem deflection_bound (ψ : RefreshField) (p : ILGParams) (ℓ : ℝ) :
    |deflection ψ p ℓ - deflection_GR ℓ|
      ≤ ((1 / 20 : ℝ) * |p.cLag * p.alpha|
            + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)) * |ℓ| := by
  have hdiff :
      deflection ψ p ℓ - deflection_GR ℓ
        = (lensing_strength ψ p - 1) * ℓ := by
    unfold deflection deflection_GR gr_lensing_strength
    ring
  have habs :
      |deflection ψ p ℓ - deflection_GR ℓ|
        = |lensing_strength ψ p - 1| * |ℓ| := by
    simpa [hdiff, abs_mul, mul_comm, mul_left_comm, mul_assoc]
  have hℓ : 0 ≤ |ℓ| := abs_nonneg ℓ
  have hstrength := lensing_strength_bound ψ p
  calc
    |deflection ψ p ℓ - deflection_GR ℓ|
        = |lensing_strength ψ p - 1| * |ℓ| := habs
    _ ≤ ((1 / 20 : ℝ) * |p.cLag * p.alpha|
          + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)) * |ℓ| :=
        mul_le_mul_of_nonneg_right hstrength hℓ

/-- If `|C_lag·α| ≤ κ`, the lensing strength deviation is bounded by `(κ/20)+(κ²/200)`. -/
theorem lensing_strength_bound_of_kappa (ψ : RefreshField) (p : ILGParams)
    (κ : ℝ) (hκ : 0 ≤ κ) (hbound : |p.cLag * p.alpha| ≤ κ) :
    |lensing_strength ψ p - 1|
      ≤ (1 / 20 : ℝ) * κ + (1 / 200 : ℝ) * κ * κ := by
  have hx_nonneg : 0 ≤ |p.cLag * p.alpha| := abs_nonneg _
  have hx_sq_le_κ : |p.cLag * p.alpha| * |p.cLag * p.alpha|
      ≤ κ * κ := by
    have hx₁ : |p.cLag * p.alpha| * |p.cLag * p.alpha|
        ≤ |p.cLag * p.alpha| * κ :=
      mul_le_mul_of_nonneg_left hbound hx_nonneg
    have hx₂ : |p.cLag * p.alpha| * κ ≤ κ * κ :=
      mul_le_mul_of_nonneg_right hbound hκ
    exact le_trans hx₁ hx₂
  have hterm₁ : (1 / 20 : ℝ) * |p.cLag * p.alpha| ≤ (1 / 20 : ℝ) * κ :=
    mul_le_mul_of_nonneg_left hbound (by norm_num)
  have hterm₂ :
      (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)
        ≤ (1 / 200 : ℝ) * (κ * κ) :=
    mul_le_mul_of_nonneg_left hx_sq_le_κ (by norm_num)
  have hsum :
      (1 / 20 : ℝ) * |p.cLag * p.alpha|
          + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)
        ≤ (1 / 20 : ℝ) * κ + (1 / 200 : ℝ) * (κ * κ) :=
    add_le_add hterm₁ hterm₂
  have base := lensing_strength_bound ψ p
  have result := base.trans hsum
  simpa using result

/-- With the same κ-bound, the deflection difference obeys the scaled inequality. -/
theorem deflection_bound_of_kappa (ψ : RefreshField) (p : ILGParams)
    (ℓ κ : ℝ) (hκ : 0 ≤ κ) (hbound : |p.cLag * p.alpha| ≤ κ) :
    |deflection ψ p ℓ - deflection_GR ℓ|
      ≤ ((1 / 20 : ℝ) * κ + (1 / 200 : ℝ) * κ * κ) * |ℓ| := by
  have base := deflection_bound ψ p ℓ
  have hx_nonneg : 0 ≤ |ℓ| := abs_nonneg ℓ
  have hx₁ : (1 / 20 : ℝ) * |p.cLag * p.alpha|
      ≤ (1 / 20 : ℝ) * κ :=
    mul_le_mul_of_nonneg_left hbound (by norm_num)
  have hx_sq_le : |p.cLag * p.alpha| * |p.cLag * p.alpha|
      ≤ κ * κ := by
    have hx_nonneg' : 0 ≤ |p.cLag * p.alpha| := abs_nonneg _
    have hx₁' : |p.cLag * p.alpha| * |p.cLag * p.alpha|
        ≤ |p.cLag * p.alpha| * κ :=
      mul_le_mul_of_nonneg_left hbound hx_nonneg'
    have hx₂' : |p.cLag * p.alpha| * κ ≤ κ * κ :=
      mul_le_mul_of_nonneg_right hbound hκ
    exact le_trans hx₁' hx₂'
  have hx₂ :
      (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)
        ≤ (1 / 200 : ℝ) * (κ * κ) :=
    mul_le_mul_of_nonneg_left hx_sq_le (by norm_num)
  have hsum :
      (1 / 20 : ℝ) * |p.cLag * p.alpha|
          + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)
        ≤ (1 / 20 : ℝ) * κ + (1 / 200 : ℝ) * (κ * κ) :=
    add_le_add hx₁ hx₂
  have hscaled := mul_le_mul_of_nonneg_right hsum hx_nonneg
  exact base.trans (by simpa using hscaled)

/-- Time-delay deviation satisfies the same bound as the deflection coefficient. -/
theorem time_delay_bound (ψ : RefreshField) (p : ILGParams) (ℓ : ℝ) :
    |time_delay ψ p ℓ - time_delay_GR ℓ|
      ≤ ((1 / 20 : ℝ) * |p.cLag * p.alpha|
            + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)) * |ℓ| := by
  have hdiff :
      time_delay ψ p ℓ - time_delay_GR ℓ
        = (lensing_strength ψ p - 1) * ℓ := by
    unfold time_delay time_delay_GR gr_lensing_strength
    ring
  have habs :
      |time_delay ψ p ℓ - time_delay_GR ℓ|
        = |lensing_strength ψ p - 1| * |ℓ| := by
    simpa [hdiff, abs_mul, mul_comm, mul_left_comm, mul_assoc]
  have hℓ : 0 ≤ |ℓ| := abs_nonneg ℓ
  have hstrength := lensing_strength_bound ψ p
  calc
    |time_delay ψ p ℓ - time_delay_GR ℓ|
        = |lensing_strength ψ p - 1| * |ℓ| := habs
    _ ≤ ((1 / 20 : ℝ) * |p.cLag * p.alpha|
          + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)) * |ℓ| :=
        mul_le_mul_of_nonneg_right hstrength hℓ

/-- κ-controlled bound for time-delay deviation. -/
theorem time_delay_bound_of_kappa (ψ : RefreshField) (p : ILGParams)
    (ℓ κ : ℝ) (hκ : 0 ≤ κ) (hbound : |p.cLag * p.alpha| ≤ κ) :
    |time_delay ψ p ℓ - time_delay_GR ℓ|
      ≤ ((1 / 20 : ℝ) * κ + (1 / 200 : ℝ) * κ * κ) * |ℓ| := by
  have base := time_delay_bound ψ p ℓ
  have hx_nonneg : 0 ≤ |ℓ| := abs_nonneg ℓ
  have hx₁ : (1 / 20 : ℝ) * |p.cLag * p.alpha| ≤ (1 / 20 : ℝ) * κ :=
    mul_le_mul_of_nonneg_left hbound (by norm_num)
  have hx_sq_le : |p.cLag * p.alpha| * |p.cLag * p.alpha| ≤ κ * κ := by
    have hx_nonneg' : 0 ≤ |p.cLag * p.alpha| := abs_nonneg _
    have hx₁' : |p.cLag * p.alpha| * |p.cLag * p.alpha|
        ≤ |p.cLag * p.alpha| * κ :=
      mul_le_mul_of_nonneg_left hbound hx_nonneg'
    have hx₂' : |p.cLag * p.alpha| * κ ≤ κ * κ :=
      mul_le_mul_of_nonneg_right hbound hκ
    exact hx₁'.trans hx₂'
  have hx₂ :
      (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)
        ≤ (1 / 200 : ℝ) * (κ * κ) :=
    mul_le_mul_of_nonneg_left hx_sq_le (by norm_num)
  have hsum :
      (1 / 20 : ℝ) * |p.cLag * p.alpha|
          + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|)
        ≤ (1 / 20 : ℝ) * κ + (1 / 200 : ℝ) * (κ * κ) :=
    add_le_add hx₁ hx₂
  have hscaled := mul_le_mul_of_nonneg_right hsum hx_nonneg
  exact base.trans (by simpa using hscaled)

/-- Absolute bound on the shear coefficient. -/
theorem shear_bound (ψ : RefreshField) (p : ILGParams) :
    |shear_coeff ψ p|
      ≤ (1 / 20 : ℝ) * |p.cLag * p.alpha|
        + (1 / 200 : ℝ) * (|p.cLag * p.alpha| * |p.cLag * p.alpha|) := by
  simpa [shear_coeff]
    using (lensing_strength_bound ψ p)

/-- κ-controlled shear bound mirroring the lensing-strength inequality. -/
theorem shear_bound_of_kappa (ψ : RefreshField) (p : ILGParams)
    (κ : ℝ) (hκ : 0 ≤ κ) (hbound : |p.cLag * p.alpha| ≤ κ) :
    |shear_coeff ψ p|
      ≤ (1 / 20 : ℝ) * κ + (1 / 200 : ℝ) * κ * κ := by
  simpa [shear_coeff]
    using lensing_strength_bound_of_kappa ψ p κ hκ hbound

/-- Simple spherical profile scaffold retained for compatibility with older
    lensing modules. -/
structure SphericalProfile where
  Φr : ℝ → ℝ
  deriving Repr

/-- Toy deflection for a spherical profile (legacy helper). -/
noncomputable def deflection_spherical (P : SphericalProfile) (b κ : ℝ) : ℝ :=
  κ * P.Φr b

@[simp] theorem deflection_spherical_eval (P : SphericalProfile) (b κ : ℝ) :
    deflection_spherical P b κ = κ * P.Φr b := rfl

/-- Legacy band lemma showing the proxy difference is trivially bounded. -/
theorem lensing_band (ψ : RefreshField) (p : ILGParams) (κ : ℝ) (hκ : 0 ≤ κ) :
    |lensing_proxy ψ p
        - baseline_potential (Phi ψ p) (Psi ψ p)| ≤ κ := by
  simpa [lensing_proxy, baseline_potential] using hκ

end ILG
end Relativity
end IndisputableMonolith
