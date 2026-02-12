import Mathlib

namespace IndisputableMonolith
namespace LNAL

/-- Falsifier flags for runtime auditing. -/
structure FalsifierFlags where
  nonNeutralWindow : Bool := false
  jIncreased       : Bool := false
  unitsLeak        : Bool := false
  consentViolation : Bool := false
deriving Repr, DecidableEq

@[simp] def FalsifierFlags.any (f : FalsifierFlags) : Bool :=
  f.nonNeutralWindow ∨ f.jIncreased ∨ f.unitsLeak ∨ f.consentViolation

end LNAL
end IndisputableMonolith
