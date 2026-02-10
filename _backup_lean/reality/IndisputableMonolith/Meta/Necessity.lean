import Mathlib
import IndisputableMonolith.Meta.Derivation
import IndisputableMonolith.Meta.AxiomLattice
import IndisputableMonolith.Meta.FromCost

namespace IndisputableMonolith
namespace Meta
namespace Necessity

/-!
# Necessity Module

Option A (2025-12-30): this module proves the *foundation necessity* side:

If an environment derives physics (in the sense of `Meta.Derivation`), then it
must include the **cost/CPM foundation flags**.
-/

/-- An environment is minimal for physics if it derives physics and no weaker
environment does -/
def MinimalForPhysics (Γ : AxiomLattice.AxiomEnv) : Prop :=
  Nonempty (AxiomLattice.DerivesWithUsage Γ Derivation.DerivesPhysics) ∧
  ∀ Δ : AxiomLattice.AxiomEnv,
    Nonempty (AxiomLattice.DerivesWithUsage Δ Derivation.DerivesPhysics) → Γ.le Δ

/-- Main necessity lemma (Option A): if an environment derives physics, it must
include T5 (unique cost) and CPM. -/
theorem necessity_lemma (Δ : AxiomLattice.AxiomEnv) :
  AxiomLattice.DerivesWithUsage Δ Derivation.DerivesPhysics →
    Δ.usesUniqueCostT5 ∧ Δ.usesCPM := by
  intro h
  obtain ⟨usage, used_le, reqCost, reqCPM, _⟩ := h
  obtain ⟨_hmp, ⟨_hat, ⟨_hcont, ⟨_hex, ⟨ht5, ⟨hcpm, _height⟩⟩⟩⟩⟩⟩ := used_le
  exact ⟨ht5 reqCost, hcpm reqCPM⟩

/-- The cost/CPM-only environment is minimal for physics. -/
def costCPMEnv : AxiomLattice.AxiomEnv := AxiomLattice.costCPMEnv

/-- cost/CPM-only environment has cost+CPM and no other flags. -/
theorem costCPMEnv_properties :
    costCPMEnv.usesUniqueCostT5 ∧ costCPMEnv.usesCPM ∧
      ¬costCPMEnv.usesMP ∧ ¬costCPMEnv.usesAtomicTick ∧
      ¬costCPMEnv.usesContinuity ∧ ¬costCPMEnv.usesExactPotential ∧
      ¬costCPMEnv.usesEightTick := by
  -- by definition, the flags are literals
  unfold costCPMEnv AxiomLattice.costCPMEnv
  simp

/-- There exists a minimal environment for physics (the cost/CPM-only one). -/
theorem exists_minimal_env_costCPM : ∃ Γf : AxiomLattice.AxiomEnv,
    Γf.usesUniqueCostT5 ∧ Γf.usesCPM ∧
      ¬Γf.usesMP ∧ ¬Γf.usesAtomicTick ∧ ¬Γf.usesContinuity ∧ ¬Γf.usesExactPotential ∧
      ¬Γf.usesEightTick ∧ MinimalForPhysics Γf := by
  refine ⟨costCPMEnv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact costCPMEnv_properties.1
  · exact costCPMEnv_properties.2.1
  · exact costCPMEnv_properties.2.2.1
  · exact costCPMEnv_properties.2.2.2.1
  · exact costCPMEnv_properties.2.2.2.2.1
  · exact costCPMEnv_properties.2.2.2.2.2.1
  · exact costCPMEnv_properties.2.2.2.2.2.2
  · -- MinimalForPhysics
    constructor
    · -- costCPMEnv derives physics (provenance witness uses costCPMEnv)
      -- Translate Sufficient to Nonempty (DerivesWithUsage _ DerivesPhysics)
      have h := AxiomLattice.costCPM_sufficient IndisputableMonolith.Constants.phi
      simp only [AxiomLattice.Sufficient, Derivation.DerivesPhysics] at h
      exact h
    · -- Any Δ deriving physics must include cost+CPM; hence costCPMEnv ≤ Δ
      intro Δ hΔ
      obtain ⟨w⟩ := hΔ
      have hNeed := necessity_lemma Δ w
      -- Build costCPMEnv ≤ Δ pointwise.
      refine ⟨False.elim, ⟨False.elim, ⟨False.elim, ⟨False.elim, ⟨?_, ⟨?_, False.elim⟩⟩⟩⟩⟩⟩
      · intro _; exact hNeed.1
      · intro _; exact hNeed.2

/-- The Minimal Axiom Theorem (Option A): cost/CPM is necessary and sufficient. -/
theorem foundation_minimal_axiom_theorem :
  ∃ Γf : AxiomLattice.AxiomEnv, Γf.usesUniqueCostT5 ∧ Γf.usesCPM ∧ MinimalForPhysics Γf := by
  rcases exists_minimal_env_costCPM with ⟨Γf, hT5, hCPM, _hmp, _hat, _hcont, _hex, _height, hmin⟩
  exact ⟨Γf, hT5, hCPM, hmin⟩

end Necessity
end Meta
end IndisputableMonolith
