import Mathlib
import IndisputableMonolith.URCGenerators.CPMClosureCert
import IndisputableMonolith.Verification.RecognitionReality

namespace IndisputableMonolith
namespace URCGenerators

/-!
# Ultimate + CPM Closure Certificate

Bundles the existence/uniqueness of the pinned scale `φ` from
`UltimateClosure` together with the cross‑domain CPM closure
certificate (Knet = 1, Cproj = 2, and domain coercivity/aggregation/positivity).

This serves as a more comprehensive top‑level certificate that
combines RS ultimate closure with CPM universality.
-/

/-- Combined certificate for UltimateClosure ∧ CPMClosure. -/
structure UltimateCPMClosureCert where
  deriving Repr

/-- Verification predicate: asserts both
    (1) unique `φ` where `UltimateClosure φ` holds, and
    (2) CPM closure across domains with RS constants. -/
@[simp] def UltimateCPMClosureCert.verified (_c : UltimateCPMClosureCert) : Prop :=
  (∃! φ : ℝ, IndisputableMonolith.Verification.RecognitionReality.UltimateClosure φ) ∧
  IndisputableMonolith.URCGenerators.CPMClosureCert.verified {}

/-- Top‑level theorem: the combined certificate verifies. -/
@[simp] theorem UltimateCPMClosureCert.verified_any (c : UltimateCPMClosureCert) :
  UltimateCPMClosureCert.verified c := by
  constructor
  · exact IndisputableMonolith.Verification.RecognitionReality.ultimate_closure_holds
  · exact IndisputableMonolith.URCGenerators.CPMClosureCert.verified_any {}

end URCGenerators
end IndisputableMonolith
