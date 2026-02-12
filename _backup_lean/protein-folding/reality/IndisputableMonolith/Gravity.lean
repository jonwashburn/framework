import IndisputableMonolith.Gravity.ILG
import IndisputableMonolith.Gravity.Rotation

/-!
# IndisputableMonolith.Gravity

Gravity module facade - re-exports core gravity formalizations:
- `Rotation`: Newtonian rotation curve identities (v² = GM/r, flat curves)
- `ILG`: Information-Limited Gravity time-kernel and weight functions

See also `IndisputableMonolith.Relativity.ILG` for the full relativistic ILG formalization
(currently sealed pending Mathlib updates).
-/

namespace IndisputableMonolith
namespace Gravity

-- Re-export key definitions
open ILG (w_t w_t_ref w_t_rescale w_t_nonneg Params ParamProps BridgeData)
open Rotation (RotSys vrot vrot_sq vrot_flat_of_linear_Menc)

end Gravity
end IndisputableMonolith
