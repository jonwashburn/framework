import Mathlib
import IndisputableMonolith.Meta.Derivation
import IndisputableMonolith.Meta.AxiomLattice
import IndisputableMonolith.Meta.FromMP
import IndisputableMonolith.Meta.Necessity

namespace IndisputableMonolith
namespace Meta

/-!
# Meta Module

This module provides the complete formalization of MP minimality:
MP is sufficient and necessary to derive physics.

The main theorem combines sufficiency (FromMP) and necessity (Necessity).
-/

/-- The Minimal Axiom Theorem (provenance form):
    There exists an environment with only MP used that derives physics;
    and any environment deriving physics must use MP, making the MP-only
    environment minimal under ≤. -/
theorem mp_minimal_axiom_theorem : ∃ Γ : AxiomLattice.AxiomEnv,
  Γ.usesMP ∧ ¬Γ.usesAtomicTick ∧ ¬Γ.usesContinuity ∧ ¬Γ.usesExactPotential ∧
  ¬Γ.usesUniqueCostT5 ∧ ¬Γ.usesEightTick ∧ Necessity.MinimalForPhysics Γ := by
  exact Necessity.exists_minimal_env_mp

end Meta
end IndisputableMonolith
