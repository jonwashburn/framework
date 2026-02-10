import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Verification.Exclusivity.NontrivialityShim
import IndisputableMonolith.Verification.Exclusivity.NoAlternatives
import IndisputableMonolith.Verification.Necessity.DiscreteNecessity
import IndisputableMonolith.Verification.Necessity.RecognitionNecessity

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity
namespace Examples

open Framework

/-!
# Example Concrete Physics Frameworks

Minimal concrete instances of `PhysicsFramework` to demonstrate how to provide
the required instances (`NonStatic`, `ObservableSensitive`).

These serve as templates for modeling real physics theories (String Theory, LQG, etc.).
-/

/-! ### Example 1: Simple Discrete Framework -/

/-- Minimal discrete framework with ℕ state space and successor dynamics. -/
def SimpleDiscrete : PhysicsFramework where
  StateSpace := ℕ
  evolve := Nat.succ
  Observable := ℕ
  measure := id
  hasInitialState := ⟨0⟩

/-- SimpleDiscrete is non-static: evolve changes every state. -/
instance : NonStatic SimpleDiscrete where
  exists_change := ⟨(0 : ℕ), Nat.succ_ne_self 0⟩

/-- SimpleDiscrete's measure reflects changes: id is injective. -/
instance : NoAlternatives.MeasureReflectsChange SimpleDiscrete where
  reflects := by
    intro s _hchg
    exact Nat.succ_ne_self s

/-! ### Example 2: Two-State Framework -/

/-- Two-state framework with flip dynamics. -/
inductive TwoState
  | state0
  | state1

def flip : TwoState → TwoState
  | TwoState.state0 => TwoState.state1
  | TwoState.state1 => TwoState.state0

def TwoStateFramework : PhysicsFramework where
  StateSpace := TwoState
  evolve := flip
  Observable := Bool
  measure := fun s => match s with
    | TwoState.state0 => false
    | TwoState.state1 => true
  hasInitialState := ⟨TwoState.state0⟩

/-- TwoStateFramework is non-static: state0 flips to state1. -/
instance : NonStatic TwoStateFramework where
  exists_change := ⟨TwoState.state0, by
    simp [TwoStateFramework, flip]⟩

/-‑! ### Instance Provision Pattern

To add instances for a new framework `MyFramework : PhysicsFramework`:

1. **NonStatic**: Prove `∃ s, MyFramework.evolve s ≠ s`
   ```lean
   instance : NonStatic MyFramework where
     exists_change := ⟨witness_state, by prove_it_changes⟩
   ```

2. **ObservableSensitive**: Prove observables detect changes
   ```lean
   instance : ObservableSensitive MyFramework my_obs where
     detects := by prove_obs_changes_when_state_changes
   ```

These instances allow the main theorems to apply to `MyFramework` without
additional hypotheses at the call site.
-/

end Examples
end Exclusivity
end Verification
end IndisputableMonolith
