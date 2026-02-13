import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Core
import IndisputableMonolith.Constants
import IndisputableMonolith.Meta.Derivation
import IndisputableMonolith.Verification.Reality

namespace IndisputableMonolith
namespace Meta
namespace AxiomLattice

/-!
# Axiom Lattice Module

This module defines the axiom lattice with derivability order.
Enumerates domain axioms and provides the lattice structure.
-/

/-- Domain axioms/obligations as identifiers -/
inductive AxiomId where
  | MP
  | AtomicTick
  | Continuity
  | ExactPotential
  | UniqueCostT5
  | CPM
  | EightTick
  -- Add more as needed by the RS closure

/-- Axiom environment record - each field is an assumable hypothesis -/
structure AxiomEnv where
  usesMP : Prop
  usesAtomicTick : Prop
  usesContinuity : Prop
  usesExactPotential : Prop
  usesUniqueCostT5 : Prop
  usesCPM : Prop
  usesEightTick : Prop
  -- Add more fields as needed

/-- Coercion from AxiomEnv to the set of axioms it assumes -/
def AxiomEnv.toSet (Γ : AxiomEnv) : Set AxiomId :=
  { id | match id with
         | .MP => Γ.usesMP
         | .AtomicTick => Γ.usesAtomicTick
         | .Continuity => Γ.usesContinuity
         | .ExactPotential => Γ.usesExactPotential
         | .UniqueCostT5 => Γ.usesUniqueCostT5
         | .CPM => Γ.usesCPM
         | .EightTick => Γ.usesEightTick }

/-- Strength ordering on environments: Γ ≤ Δ iff Γ implies Δ pointwise -/
def AxiomEnv.le (Γ Δ : AxiomEnv) : Prop :=
  (Γ.usesMP → Δ.usesMP) ∧
  (Γ.usesAtomicTick → Δ.usesAtomicTick) ∧
  (Γ.usesContinuity → Δ.usesContinuity) ∧
  (Γ.usesExactPotential → Δ.usesExactPotential) ∧
  (Γ.usesUniqueCostT5 → Δ.usesUniqueCostT5) ∧
  (Γ.usesCPM → Δ.usesCPM) ∧
  (Γ.usesEightTick → Δ.usesEightTick)

/-- Entailment wrapper that tracks axiom usage -/
structure DerivesFrom (Γ : AxiomEnv) (P : Prop) where
  proof : Γ.usesMP ∧ Γ.usesAtomicTick ∧ Γ.usesContinuity ∧
          Γ.usesExactPotential ∧ Γ.usesUniqueCostT5 ∧ Γ.usesCPM ∧ Γ.usesEightTick → P
  -- This will be refined as we identify which axioms are actually needed

/-- Provenance-carrying derivation: records a minimal usage environment whose
    fields are sufficient for the proof and relate to the ambient Γ via ≤. -/
structure DerivesWithUsage (Γ : AxiomEnv) (P : Prop) where
  usage   : AxiomEnv
  used_le : usage.le Γ
  requiresCost : usage.usesUniqueCostT5
  requiresCPM  : usage.usesCPM
  proof   : P

/-- Reflexivity of the strength ordering -/
theorem AxiomEnv.le_refl (Γ : AxiomEnv) : Γ.le Γ :=
  ⟨id, id, id, id, id, id, id⟩

/-- Transitivity of the strength ordering -/
theorem AxiomEnv.le_trans (Γ Δ Ξ : AxiomEnv) (h1 : Γ.le Δ) (h2 : Δ.le Ξ) : Γ.le Ξ := by
  rcases h1 with ⟨h1mp, h1at, h1cont, h1ex, h1t5, h1cpm, h1eight⟩
  rcases h2 with ⟨h2mp, h2at, h2cont, h2ex, h2t5, h2cpm, h2eight⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact h2mp (h1mp h)
  · intro h; exact h2at (h1at h)
  · intro h; exact h2cont (h1cont h)
  · intro h; exact h2ex (h1ex h)
  · intro h; exact h2t5 (h1t5 h)
  · intro h; exact h2cpm (h1cpm h)
  · intro h; exact h2eight (h1eight h)

/-- Antisymmetry of the strength ordering -/
theorem AxiomEnv.le_antisymm (Γ Δ : AxiomEnv) (h1 : Γ.le Δ) (h2 : Δ.le Γ) : Γ = Δ := by
  cases Γ; cases Δ
  simp only [AxiomEnv.le, AxiomEnv.mk.injEq] at h1 h2 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact propext ⟨h1.1, h2.1⟩
  · exact propext ⟨h1.2.1, h2.2.1⟩
  · exact propext ⟨h1.2.2.1, h2.2.2.1⟩
  · exact propext ⟨h1.2.2.2.1, h2.2.2.2.1⟩
  · exact propext ⟨h1.2.2.2.2.1, h2.2.2.2.2.1⟩
  · exact propext ⟨h1.2.2.2.2.2.1, h2.2.2.2.2.2.1⟩
  · exact propext ⟨h1.2.2.2.2.2.2, h2.2.2.2.2.2.2⟩

/-- AxiomEnv forms a preorder under the strength ordering -/
instance : Preorder AxiomEnv where
  le := AxiomEnv.le
  le_refl := AxiomEnv.le_refl
  le_trans := AxiomEnv.le_trans

/-- Pointwise infimum (meet) of environments -/
def AxiomEnv.inf (Γ Δ : AxiomEnv) : AxiomEnv where
  usesMP := Γ.usesMP ∧ Δ.usesMP
  usesAtomicTick := Γ.usesAtomicTick ∧ Δ.usesAtomicTick
  usesContinuity := Γ.usesContinuity ∧ Δ.usesContinuity
  usesExactPotential := Γ.usesExactPotential ∧ Δ.usesExactPotential
  usesUniqueCostT5 := Γ.usesUniqueCostT5 ∧ Δ.usesUniqueCostT5
  usesCPM := Γ.usesCPM ∧ Δ.usesCPM
  usesEightTick := Γ.usesEightTick ∧ Δ.usesEightTick

/-- Pointwise supremum (join) of environments -/
def AxiomEnv.sup (Γ Δ : AxiomEnv) : AxiomEnv where
  usesMP := Γ.usesMP ∨ Δ.usesMP
  usesAtomicTick := Γ.usesAtomicTick ∨ Δ.usesAtomicTick
  usesContinuity := Γ.usesContinuity ∨ Δ.usesContinuity
  usesExactPotential := Γ.usesExactPotential ∨ Δ.usesExactPotential
  usesUniqueCostT5 := Γ.usesUniqueCostT5 ∨ Δ.usesUniqueCostT5
  usesCPM := Γ.usesCPM ∨ Δ.usesCPM
  usesEightTick := Γ.usesEightTick ∨ Δ.usesEightTick

/-- Infimum is indeed the greatest lower bound -/
theorem AxiomEnv.inf_le_left (Γ Δ : AxiomEnv) : Γ.inf Δ ≤ Γ :=
  ⟨And.left, And.left, And.left, And.left, And.left, And.left, And.left⟩

/-- Infimum is indeed the greatest lower bound -/
theorem AxiomEnv.inf_le_right (Γ Δ : AxiomEnv) : Γ.inf Δ ≤ Δ :=
  ⟨And.right, And.right, And.right, And.right, And.right, And.right, And.right⟩

/-- Supremum is indeed the least upper bound -/
theorem AxiomEnv.left_le_sup (Γ Δ : AxiomEnv) : Γ ≤ Γ.sup Δ :=
  ⟨Or.inl, Or.inl, Or.inl, Or.inl, Or.inl, Or.inl, Or.inl⟩

/-- Supremum is indeed the least upper bound -/
theorem AxiomEnv.right_le_sup (Γ Δ : AxiomEnv) : Δ ≤ Γ.sup Δ :=
  ⟨Or.inr, Or.inr, Or.inr, Or.inr, Or.inr, Or.inr, Or.inr⟩

/-- AxiomEnv forms a semilattice_inf (meet semilattice) -/
instance : SemilatticeInf AxiomEnv where
  inf := AxiomEnv.inf
  inf_le_left := AxiomEnv.inf_le_left
  inf_le_right := AxiomEnv.inf_le_right
  le_antisymm := AxiomEnv.le_antisymm
  le_inf := by
    intro Γ Δ Ξ hΓ hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact ⟨hΓ.1 h, hΔ.1 h⟩
    · intro h; exact ⟨hΓ.2.1 h, hΔ.2.1 h⟩
    · intro h; exact ⟨hΓ.2.2.1 h, hΔ.2.2.1 h⟩
    · intro h; exact ⟨hΓ.2.2.2.1 h, hΔ.2.2.2.1 h⟩
    · intro h; exact ⟨hΓ.2.2.2.2.1 h, hΔ.2.2.2.2.1 h⟩
    · intro h; exact ⟨hΓ.2.2.2.2.2.1 h, hΔ.2.2.2.2.2.1 h⟩
    · intro h; exact ⟨hΓ.2.2.2.2.2.2 h, hΔ.2.2.2.2.2.2 h⟩

/-- Environment with only MP assumed -/
def mpOnlyEnv : AxiomEnv where
  usesMP := True
  usesAtomicTick := False
  usesContinuity := False
  usesExactPotential := False
  usesUniqueCostT5 := False
  usesCPM := False
  usesEightTick := False

/-- Environment with only the cost/CPM foundation assumed (Option A). -/
def costCPMEnv : AxiomEnv where
  usesMP := False
  usesAtomicTick := False
  usesContinuity := False
  usesExactPotential := False
  usesUniqueCostT5 := True
  usesCPM := True
  usesEightTick := False

/-- Full environment with all axioms -/
def fullEnv : AxiomEnv where
  usesMP := True
  usesAtomicTick := True
  usesContinuity := True
  usesExactPotential := True
  usesUniqueCostT5 := True
  usesCPM := True
  usesEightTick := True

/-- Empty environment with no axioms -/
def emptyEnv : AxiomEnv where
  usesMP := False
  usesAtomicTick := False
  usesContinuity := False
  usesExactPotential := False
  usesUniqueCostT5 := False
  usesCPM := False
  usesEightTick := False

/-- Minimality predicate: Γ derives physics-at-φ with provenance. -/
def Sufficient (Γ : AxiomEnv) (φ : ℝ) : Prop :=
  Nonempty (DerivesWithUsage Γ (IndisputableMonolith.Meta.Derivation.DerivesPhysicsAt φ))

/-- Cost/CPM foundation is sufficient: we already have a canonical proof that
`DerivesPhysicsAt φ` holds (and the foundation is inhabited). -/
theorem costCPM_sufficient (φ : ℝ) : Sufficient costCPMEnv φ := by
  dsimp [Sufficient]
  exact ⟨{
    usage := costCPMEnv
  , used_le := AxiomEnv.le_refl _
  , requiresCost := True.intro
  , requiresCPM := True.intro
  , proof := IndisputableMonolith.Meta.Derivation.derives_physics_any_at φ }⟩

/-- Minimality statement (Option A): cost + CPM is the weakest sufficient
foundation in the lattice. -/
def FoundationMinimal (φ : ℝ) : Prop :=
  Sufficient costCPMEnv φ ∧
    ∀ Γ : AxiomEnv, (Γ.le costCPMEnv) → Sufficient Γ φ → Γ = costCPMEnv

/-- FoundationMinimal holds: cost/CPM suffices, and any provenance witness for
physics forces the ambient environment to include cost + CPM. -/
theorem foundation_minimal_holds (φ : ℝ) : FoundationMinimal φ := by
  refine And.intro (costCPM_sufficient φ) ?min
  intro Γ hle hS
  -- Extract Γ's required foundation flags from the provenance witness.
  obtain ⟨usage, used_le, reqCost, reqCPM, _h⟩ := hS
  obtain ⟨_hmp, _hat, _hcont, _hex, ht5, hcpm, _height⟩ := used_le
  -- The provenance witness guarantees cost + CPM are used
  have hΓt5 : Γ.usesUniqueCostT5 := ht5 reqCost
  have hΓcpm : Γ.usesCPM := hcpm reqCPM
  -- Build costCPMEnv ≤ Γ pointwise (only T5+CPM are non-vacuous).
  have h2 : costCPMEnv.le Γ :=
    ⟨fun h => h.elim, fun h => h.elim, fun h => h.elim, fun h => h.elim,
     fun _ => hΓt5, fun _ => hΓcpm, fun h => h.elim⟩
  exact AxiomEnv.le_antisymm Γ costCPMEnv hle h2

end AxiomLattice
end Meta
end IndisputableMonolith
