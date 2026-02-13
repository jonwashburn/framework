import Mathlib
import IndisputableMonolith.Gravity.ILG

namespace IndisputableMonolith
namespace TruthCore

/-- Alias: time-kernel ratio is dimensionless (invariant under common rescaling). -/
theorem time_kernel_dimensionless (c T τ : ℝ) (hc : 0 < c) :
  IndisputableMonolith.Gravity.ILG.w_time_ratio (c * T) (c * τ)
    = IndisputableMonolith.Gravity.ILG.w_time_ratio T τ := by
  simpa using IndisputableMonolith.Gravity.ILG.w_time_ratio_rescale (c:=c) (Tdyn:=T) (τ0:=τ) hc

end TruthCore
end IndisputableMonolith

