import Mathlib
import IndisputableMonolith.Meta.AxiomLattice
import IndisputableMonolith.Meta.Derivation

namespace IndisputableMonolith
namespace Meta
namespace FromCost

/-!
# FromCost (Option A)

Sufficiency wrappers for the new foundation:

If an axiom environment provides the **cost/CPM foundation flags**, then it
derives physics (in the RS sense of `Meta.Derivation.DerivesPhysicsAt`).

This is intentionally lightweight: the proof object is already available as
`Derivation.derives_physics_any_at`; the only work here is tracking provenance
through the `AxiomLattice` plumbing.
-/

/-- From an environment that includes the cost/CPM foundation flags, derive physics-at-φ
with a provenance witness whose `usage` is exactly `AxiomLattice.costCPMEnv`. -/
def derives_physics_from_costCPM_with_usage
  (Γ : AxiomLattice.AxiomEnv)
  (hT5 : Γ.usesUniqueCostT5)
  (hCPM : Γ.usesCPM)
  (φ : ℝ) :
  AxiomLattice.DerivesWithUsage Γ (Derivation.DerivesPhysicsAt φ) :=
{ usage := AxiomLattice.costCPMEnv
, used_le := ⟨False.elim, False.elim, False.elim, False.elim, fun _ => hT5, fun _ => hCPM, False.elim⟩
, requiresCost := True.intro
, requiresCPM := True.intro
, proof := Derivation.derives_physics_any_at φ
}

/-- Drop provenance: from cost/CPM flags, obtain the raw physics derivation. -/
theorem derives_physics_from_costCPM
  (Γ : AxiomLattice.AxiomEnv)
  (hT5 : Γ.usesUniqueCostT5)
  (hCPM : Γ.usesCPM)
  (φ : ℝ) :
  Derivation.DerivesPhysicsAt φ :=
  (derives_physics_from_costCPM_with_usage Γ hT5 hCPM φ).proof

end FromCost
end Meta
end IndisputableMonolith
