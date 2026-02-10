import Mathlib
import IndisputableMonolith.Cost.JcostCore
import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Consciousness.ConsciousnessHamiltonian

/-!
# Light-Memory: Zero-Cost Equilibrium and Ground State Properties
-/

namespace IndisputableMonolith.Consciousness

open Foundation

/-- Light-memory is the J(1)=0 equilibrium state for a recognition pattern. -/
structure LightMemoryState where
  pattern : RecognitionPattern
  storedAt : ℝ
  cost_zero : J 1 = 0

/-- Zero-cost equilibrium: J(1)=0 from cost uniqueness and normalization. -/
lemma J_one_eq_zero : J 1 = 0 := by
  -- Use canonical J-cost identity
  simpa [J] using IndisputableMonolith.Cost.Jcost_unit0

/-- Maintenance cost of light-memory ground state is zero. -/
def lightMemoryCost (lm : LightMemoryState) : ℝ := 0

/-- Boundary → light-memory transition preserves Z-pattern. -/
def toLightMemory (b : StableBoundary) (t : ℝ) : LightMemoryState :=
  { pattern := b.pattern, storedAt := t, cost_zero := J_one_eq_zero }

/-- Z-invariant preserved by transition to light-memory. -/
lemma Z_preserved_to_light (b : StableBoundary) (t : ℝ) :
    Z_invariant (toLightMemory b t).pattern = Z_invariant b.pattern := rfl

/-- Light-memory is a minimizer versus any positive-maintenance boundary. -/
lemma dissolution_prefers_light (b : StableBoundary) (t : ℝ) :
    lightMemoryCost (toLightMemory b t) ≤ RecognitionCost b := by
  -- `lightMemoryCost` is definitionally `0`, so it suffices that `RecognitionCost b ≥ 0`,
  -- which is already proved in `ConsciousnessHamiltonian`.
  simpa [lightMemoryCost] using (recognition_cost_nonneg b)

end IndisputableMonolith.Consciousness
