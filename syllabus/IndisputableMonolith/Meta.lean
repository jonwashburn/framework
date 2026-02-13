import Mathlib
import IndisputableMonolith.Meta.Derivation
import IndisputableMonolith.Meta.AxiomLattice
import IndisputableMonolith.Meta.FromCost
import IndisputableMonolith.Meta.Necessity

namespace IndisputableMonolith
namespace Meta

/-!
# Meta Module

Option A (2025-12-30): this module provides the **cost/CPM foundation minimality**
result:

The cost/CPM foundation is sufficient and necessary (in the provenance lattice)
to derive physics.
-/

/-- The Minimal Foundation Theorem (Option A, provenance form):

There exists an environment whose only positive flags are:
- `usesUniqueCostT5`
- `usesCPM`

and this environment is minimal (under `≤`) among those that derive physics. -/
theorem foundation_minimal_axiom_theorem : ∃ Γ : AxiomLattice.AxiomEnv,
  Γ.usesUniqueCostT5 ∧ Γ.usesCPM ∧ Necessity.MinimalForPhysics Γ := by
  exact Necessity.foundation_minimal_axiom_theorem

end Meta
end IndisputableMonolith
