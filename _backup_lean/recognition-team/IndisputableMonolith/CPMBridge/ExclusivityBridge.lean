import Mathlib
import IndisputableMonolith.Verification.CPMBridge.Initiality
import IndisputableMonolith.Verification.Exclusivity.NoAlternatives

/-!
# CPM ⇒ RS via Exclusivity (Bridge Wrapper)

This wrapper connects the CPM initiality-style universality check to the
physics-side exclusivity theorem. It gives a clean surface theorem that
under the usual framework hypotheses, any zero-parameter framework that
derives observables is equivalent (up to units) to the RS framework.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPMBridge
namespace ExclusivityBridge

open IndisputableMonolith.Verification.CPMBridge.Initiality
open IndisputableMonolith.Verification.Exclusivity

/-- If a physics framework `F` is zero-parameter, derives observables,
    and satisfies the standard self-similarity/nontriviality assumptions,
    then by the exclusivity theorem it is equivalent to the RS framework.

    This repackages `no_alternative_frameworks` with explicit arguments. -/
theorem framework_reduces_to_RS
  (F : Framework.PhysicsFramework)
  [Inhabited F.StateSpace]
  [Framework.NonStatic F]
  (hZero : Framework.HasZeroParameters F)
  [Framework.MeasureReflectsChange F]
  (hObs : Framework.DerivesObservables F)
  (hSelfSim : Necessity.PhiNecessity.HasSelfSimilarity F.StateSpace) :
  ∃ (φ : ℝ) (equiv_framework : Framework.PhysicsFramework),
    Framework.FrameworkEquiv F equiv_framework := by
  -- direct call to the main exclusivity theorem
  exact NoAlternatives.no_alternative_frameworks (F:=F)
    (hZero:=hZero) (hObs:=hObs) (hSelfSim:=hSelfSim)

end ExclusivityBridge
end CPMBridge
end Verification
end IndisputableMonolith
