import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Verification

namespace IndisputableMonolith
namespace Verification

/-- The two route displays agree identically as observables (bridge-level K-gate). -/
theorem k_gate_bridge_theorem : ∀ U, BridgeEval K_A_obs U = BridgeEval K_B_obs U := by
  intro U
  simp [BridgeEval, K_A_obs, K_B_obs]

end Verification
end IndisputableMonolith
