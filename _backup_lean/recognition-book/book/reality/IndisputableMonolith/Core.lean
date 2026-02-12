import Mathlib
import IndisputableMonolith.Core.ConstantsAndPatterns
import IndisputableMonolith.Core.Streams
import IndisputableMonolith.Core.RS
import IndisputableMonolith.Core.Complexity
import IndisputableMonolith.Core.URC
import IndisputableMonolith.Core.Recognition
import IndisputableMonolith.Ethics.Invariants

namespace IndisputableMonolith
/-! ### Core umbrella: imports stable submodules only. -/

/-! #### Ethics invariants -/
namespace Ethics
namespace Invariants

abbrev Monotonicity : Prop := IndisputableMonolith.Ethics.Invariants.Monotonicity
abbrev Symmetry     : Prop := IndisputableMonolith.Ethics.Invariants.Symmetry
abbrev Stability    : Prop := IndisputableMonolith.Ethics.Invariants.Stability

abbrev All : Prop := IndisputableMonolith.Ethics.Invariants.All

@[simp] lemma monotonicity_holds : Monotonicity := IndisputableMonolith.Ethics.Invariants.monotonicity_holds
@[simp] lemma symmetry_holds     : Symmetry     := IndisputableMonolith.Ethics.Invariants.symmetry_holds
@[simp] lemma stability_holds    : Stability    := IndisputableMonolith.Ethics.Invariants.stability_holds

@[simp] lemma all_holds : All := IndisputableMonolith.Ethics.Invariants.all_holds

end Invariants
end Ethics

/-! #### Compatibility aliases kept minimal -/
abbrev Pattern (d : Nat) := Patterns.Pattern d
abbrev CompleteCover := Patterns.CompleteCover

end IndisputableMonolith
