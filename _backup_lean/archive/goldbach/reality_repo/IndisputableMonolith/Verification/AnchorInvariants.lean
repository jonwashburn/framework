import Mathlib
import IndisputableMonolith.Verification

namespace IndisputableMonolith
namespace Verification

theorem dimless_anchor_invariant_KA {U U'} (h : UnitsRescaled U U') :
  BridgeEval K_A_obs U = BridgeEval K_A_obs U' := anchor_invariance K_A_obs h

theorem dimless_anchor_invariant_KB {U U'} (h : UnitsRescaled U U') :
  BridgeEval K_B_obs U = BridgeEval K_B_obs U' := anchor_invariance K_B_obs h

end Verification
end IndisputableMonolith
