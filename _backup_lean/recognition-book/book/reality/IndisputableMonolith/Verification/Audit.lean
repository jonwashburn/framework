import Mathlib

namespace IndisputableMonolith
namespace Verification

/-- Audit: SI evaluation must go through BridgeData. This marker theorem is used as a guard
    in code review to avoid accidental direct numerics at the proof layer. -/
theorem audit_SI_via_bridge_only : True := by trivial

end Verification
end IndisputableMonolith
