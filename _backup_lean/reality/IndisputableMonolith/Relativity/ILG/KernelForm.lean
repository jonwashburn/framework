import Mathlib
import IndisputableMonolith.ILG.ParamsKernel
import IndisputableMonolith.Relativity.ILG.WeakField

namespace IndisputableMonolith
namespace Relativity
namespace ILG

open scoped Real

noncomputable section

-- WeakField definitions are in the same ILG namespace

/-- Explicit time-kernel formula `w_t = 1 + C_lag · (max(εt, T_dyn/τ₀))^α`.

This simply unfolds the definition from `ILG.WeakField`.  It is exposed here so
downstream certificates can rely on a named theorem rather than rewriting by `rfl` in
multiple locations. -/
@[simp] theorem time_kernel_explicit (P : Params) (Tdyn τ0 : ℝ) :
  w_t P Tdyn τ0
    = 1 + P.Clag * (max εt (Tdyn / τ0)) ^ P.alpha := by
  rfl

/-- Time-kernel is normalised at the reference cadence: `w_t(T = τ₀, τ₀) = 1` when τ₀/τ₀ = 1 ≥ εt. -/
@[simp] theorem time_kernel_reference (P : Params) (τ0 : ℝ) (hτ : τ0 ≠ 0) (hε : εt ≤ 1) :
  w_t P τ0 τ0 = 1 + P.Clag := by
  unfold w_t
  have h1 : τ0 / τ0 = 1 := div_self hτ
  have h2 : max εt (τ0 / τ0) = 1 := by
    rw [h1]
    exact max_eq_right hε
  simp only [h2, Real.one_rpow, mul_one]

/-- Time-kernel is dimensionless: scaling `T_dyn` and `τ₀` by the same positive factor
leaves `w_t` unchanged. -/
@[simp] theorem time_kernel_rescale (P : Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  w_t P (c * Tdyn) (c * τ0) = w_t P Tdyn τ0 := by
  unfold w_t
  -- (c * Tdyn) / (c * τ0) = Tdyn / τ0
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have h : c * Tdyn / (c * τ0) = Tdyn / τ0 := by field_simp [hc_ne]
  simp only [h]

/-- Time-kernel is nonnegative whenever the ILG parameter bundle satisfies the standard
positivity bounds (`ParamProps`). -/
theorem time_kernel_nonneg (P : Params) (hP : ParamProps P)
    (Tdyn τ0 : ℝ) : 0 ≤ w_t P Tdyn τ0 := by
  unfold w_t
  have hmax_pos : 0 < max εt (Tdyn / τ0) := lt_max_of_lt_left epsilon_t_pos
  have hpow_nonneg : 0 ≤ (max εt (Tdyn / τ0)) ^ P.alpha :=
    Real.rpow_nonneg (le_of_lt hmax_pos) P.alpha
  have hcorr : 0 ≤ P.Clag * (max εt (Tdyn / τ0)) ^ P.alpha :=
    mul_nonneg hP.Clag_nonneg hpow_nonneg
  linarith

/-- Consistency with the weak-field rotation identity: using the time-kernel as the
weight rescales baryonic squared velocity multiplicatively. -/
theorem time_kernel_rotation_consistent (P : Params)
    (v_baryon2 Tdyn τ0 : ℝ) :
    v_model2 v_baryon2 (w_t P Tdyn τ0)
      = w_t P Tdyn τ0 * v_baryon2 := by
  simp [v_model2]

end

end ILG
end Relativity
end IndisputableMonolith
