import Mathlib
import IndisputableMonolith.Bridge.Data

namespace IndisputableMonolith
namespace Bridge
namespace BridgeDataExt

open IndisputableMonolith.BridgeData

@[simp] def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  IndisputableMonolith.BridgeData.passAt B u_ell0 u_lrec k

end BridgeDataExt
end Bridge
end IndisputableMonolith
