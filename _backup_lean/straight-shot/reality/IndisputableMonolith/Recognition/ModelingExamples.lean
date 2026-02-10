import Mathlib
import IndisputableMonolith.Recognition

namespace IndisputableMonolith
namespace ModelingExamples

open Recognition

/-- A simple 2-vertex recognition structure with bidirectional relation. -/
def SimpleStructure : RecognitionStructure := {
  U := Bool,
  R := fun a b => a ≠ b
}

/-- A balanced ledger on the simple structure. -/
def SimpleLedger : Ledger SimpleStructure := {
  debit := fun _ => 1,
  credit := fun _ => 0
}

/-- The simple structure satisfies conservation on closed chains. -/
instance : Conserves SimpleLedger := {
  conserve := by
    intro ch hclosed
    simp [chainFlux, phi]
    -- For any closed chain, head = last, so flux = 0
    rw [hclosed]
    ring
}

/-- A simple tick schedule alternating between the two vertices. -/
def SimpleTicks : Nat → Bool → Prop := fun t v => v = (t % 2 == 1)

instance : AtomicTick SimpleStructure := {
  postedAt := SimpleTicks,
  unique_post := by
    intro t
    use (t % 2 == 1)
    constructor
    · rfl
    · intro u hu
      simp [SimpleTicks] at hu
      exact hu
}

/-- Example of BoundedStep on Bool with degree 1. -/
instance : BoundedStep Bool 1 := {
  step := SimpleStructure.R,
  neighbors := fun b => if b then {false} else {true},
  step_iff_mem := by
    intro a b
    simp [SimpleStructure]
    cases a <;> cases b <;> simp
}

end ModelingExamples
end IndisputableMonolith
