import Mathlib
import IndisputableMonolith.ILG.ParamsKernel
import IndisputableMonolith.Relativity.ILG.WeakField

namespace IndisputableMonolith
namespace Relativity
namespace ILG

open scoped Real

namespace Core := IndisputableMonolith.ILG

noncomputable section

/-- Explicit time-kernel formula `w_t = 1 + C_lag · ((T_dyn/τ₀)^α - 1)`.

This simply unfolds the definition from `ILG.ParamsKernel`.  It is exposed here so
downstream certificates can rely on a named theorem rather than rewriting by `rfl` in
multiple locations. -/
@[simp] theorem time_kernel_explicit (P : Core.Params) (Tdyn τ0 : ℝ) :
  Core.w_t P Tdyn τ0
    = 1 + P.Clag * (Real.rpow (max Core.εt (Tdyn / τ0)) P.alpha - 1) := rfl

/-- Time-kernel is normalised at the reference cadence: `w_t(T = τ₀, τ₀) = 1`. -/
@[simp] theorem time_kernel_reference (P : Core.Params) (τ0 : ℝ) :
  Core.w_t P τ0 τ0 = 1 := Core.w_t_ref P τ0

/-- Time-kernel is dimensionless: scaling `T_dyn` and `τ₀` by the same positive factor
leaves `w_t` unchanged. -/
@[simp] theorem time_kernel_rescale (P : Core.Params) (c Tdyn τ0 : ℝ) (hc : 0 < c) :
  Core.w_t P (c * Tdyn) (c * τ0) = Core.w_t P Tdyn τ0 :=
  Core.w_t_rescale P c Tdyn τ0 hc

/-- Time-kernel is nonnegative whenever the ILG parameter bundle satisfies the standard
positivity bounds (`ParamProps`). -/
theorem time_kernel_nonneg (P : Core.Params) (hP : Core.ParamProps P)
    (Tdyn τ0 : ℝ) : 0 ≤ Core.w_t P Tdyn τ0 :=
  Core.w_t_nonneg P hP Tdyn τ0

/-- Consistency with the weak-field rotation identity: using the time-kernel as the
weight rescales baryonic squared velocity multiplicatively. -/
theorem time_kernel_rotation_consistent (P : Core.Params)
    (v_baryon2 Tdyn τ0 : ℝ) :
    v_model2 v_baryon2 (Core.w_t P Tdyn τ0)
      = Core.w_t P Tdyn τ0 * v_baryon2 := by
  simp [v_model2]

end

end ILG
end Relativity
end IndisputableMonolith
