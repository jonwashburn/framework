import Mathlib
import IndisputableMonolith.Bridge.Basic

namespace IndisputableMonolith.Bridge
namespace BridgeDataExt

open IndisputableMonolith.Bridge.BridgeData

@[simp] def u_comb (B : BridgeData) (u_ell0 u_lrec : ℝ) : ℝ :=
  Real.sqrt (u_ell0^2 + u_lrec^2)

@[simp] def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  let KA := K_A B; let KB := K_B B; let u := u_comb B u_ell0 u_lrec
  decide ((Real.abs (KA - KB)) / (k * u) ≤ 1)

end BridgeDataExt
end IndisputableMonolith.Bridge
