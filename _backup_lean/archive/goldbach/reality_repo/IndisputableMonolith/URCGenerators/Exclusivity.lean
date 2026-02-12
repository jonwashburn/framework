import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Verification.Exclusivity
import IndisputableMonolith.Verification.Identifiability

namespace IndisputableMonolith
namespace URCGenerators

/‑! Certificates for exclusivity and identifiability scaffolds. -/

structure ExclusiveRealityCert where
  deriving Repr

@[simp] def ExclusiveRealityCert.verified (_c : ExclusiveRealityCert) : Prop :=
  IndisputableMonolith.Verification.Exclusivity.ExclusiveReality

@[simp] theorem ExclusiveRealityCert.verified_any (c : ExclusiveRealityCert) :
  ExclusiveRealityCert.verified c :=
  IndisputableMonolith.Verification.Exclusivity.exclusive_reality_holds

structure IdentifiabilityCert where
  deriving Repr

@[simp] def IdentifiabilityCert.verified (_c : IdentifiabilityCert) : Prop :=
  IndisputableMonolith.Verification.Identifiability.IdentifiableAt IndisputableMonolith.Constants.phi

@[simp] theorem IdentifiabilityCert.verified_any (c : IdentifiabilityCert) :
  IdentifiabilityCert.verified c :=
  IndisputableMonolith.Verification.Identifiability.identifiable_at_any IndisputableMonolith.Constants.phi

end URCGenerators
end IndisputableMonolith

