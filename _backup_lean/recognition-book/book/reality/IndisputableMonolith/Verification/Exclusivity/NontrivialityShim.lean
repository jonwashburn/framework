import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Verification.Necessity.RecognitionNecessity

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity

/-!
Mild dynamical non-constancy assumption -> non-trivial observable.

If `measure ∘ evolve` is not injective (there exist s₁ ≠ s₂ with same measured
value after one step), then either `measure` itself is non-constant or the
composition differs on the preimages, yielding a pair with distinct values.
We export a small lemma that produces distinct observable values under a
minimal hypothesis.
-/

def compose_measure {F : Framework.PhysicsFramework}
  (obs : Necessity.RecognitionNecessity.Observable F.StateSpace)
  : F.StateSpace → ℝ := fun s => obs.value (F.evolve s)

/-! Bridge class: observables that detect any change in state. -/

class ObservableSensitive (F : Framework.PhysicsFramework)
  (obs : Necessity.RecognitionNecessity.Observable F.StateSpace) : Prop where
  detects : ∀ s : F.StateSpace, F.evolve s ≠ s →
    obs.value (F.evolve s) ≠ obs.value s

/-- From `NonStatic` and `ObservableSensitive`, obtain a one‑step observable change. -/
theorem obs_changes_if_nonstatic
  (F : Framework.PhysicsFramework)
  (obs : Necessity.RecognitionNecessity.Observable F.StateSpace)
  [Framework.NonStatic F]
  [ObservableSensitive F obs]
  : ∃ s : F.StateSpace, obs.value (F.evolve s) ≠ obs.value s := by
  rcases (Framework.NonStatic.exists_change (F:=F)) with ⟨s, hchg⟩
  exact ⟨s, ObservableSensitive.detects s hchg⟩

/-- One‑step observable change implies distinct observable values for some pair. -/
theorem distinct_states_for_observable
  (F : Framework.PhysicsFramework)
  (obs : Necessity.RecognitionNecessity.Observable F.StateSpace)
  (h : ∃ s : F.StateSpace, obs.value (F.evolve s) ≠ obs.value s) :
  ∃ s₁ s₂ : F.StateSpace, obs.value s₁ ≠ obs.value s₂ := by
  exact Necessity.RecognitionNecessity.evolve_changes_observable_implies_distinct F obs h

end Exclusivity
end Verification
end IndisputableMonolith
