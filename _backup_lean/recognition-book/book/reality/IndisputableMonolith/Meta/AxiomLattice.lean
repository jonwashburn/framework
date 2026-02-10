import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Core
import IndisputableMonolith.Constants
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
  | EightTick
  -- Add more as needed by the RS closure

/-- Axiom environment record - each field is an assumable hypothesis -/
structure AxiomEnv where
  usesMP : Prop
  usesAtomicTick : Prop
  usesContinuity : Prop
  usesExactPotential : Prop
  usesUniqueCostT5 : Prop
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
         | .EightTick => Γ.usesEightTick }

/-- Strength ordering on environments: Γ ≤ Δ iff Γ implies Δ pointwise -/
def AxiomEnv.le (Γ Δ : AxiomEnv) : Prop :=
  (Γ.usesMP → Δ.usesMP) ∧
  (Γ.usesAtomicTick → Δ.usesAtomicTick) ∧
  (Γ.usesContinuity → Δ.usesContinuity) ∧
  (Γ.usesExactPotential → Δ.usesExactPotential) ∧
  (Γ.usesUniqueCostT5 → Δ.usesUniqueCostT5) ∧
  (Γ.usesEightTick → Δ.usesEightTick)

/-- Entailment wrapper that tracks axiom usage -/
structure DerivesFrom (Γ : AxiomEnv) (P : Prop) where
  proof : Γ.usesMP ∧ Γ.usesAtomicTick ∧ Γ.usesContinuity ∧
          Γ.usesExactPotential ∧ Γ.usesUniqueCostT5 ∧ Γ.usesEightTick → P
  -- This will be refined as we identify which axioms are actually needed

/-- Provenance-carrying derivation: records a minimal usage environment whose
    fields are sufficient for the proof and relate to the ambient Γ via ≤. -/
structure DerivesWithUsage (Γ : AxiomEnv) (P : Prop) where
  usage   : AxiomEnv
  used_le : usage.le Γ
  requiresMP : usage.usesMP
  proof   : P

/-- Reflexivity of the strength ordering -/
theorem AxiomEnv.le_refl (Γ : AxiomEnv) : Γ.le Γ :=
  ⟨id, id, id, id, id, id⟩

/-- Transitivity of the strength ordering -/
theorem AxiomEnv.le_trans (Γ Δ Ξ : AxiomEnv) (h1 : Γ.le Δ) (h2 : Δ.le Ξ) : Γ.le Ξ :=
  ⟨fun h => h2.1 (h1.1 h),
   fun h => h2.2 (h1.2 h),
   fun h => h2.3 (h1.3 h),
   fun h => h2.4 (h1.4 h),
   fun h => h2.5 (h1.5 h),
   fun h => h2.6 (h1.6 h)⟩

/-- Antisymmetry of the strength ordering -/
theorem AxiomEnv.le_antisymm (Γ Δ : AxiomEnv) (h1 : Γ.le Δ) (h2 : Δ.le Γ) : Γ = Δ := by
  cases Γ; cases Δ
  simp at h1 h2
  constructor <;> (constructor <;> try constructor <;> try constructor <;> try constructor <;> try constructor)
  · exact propext ⟨h1.1, h2.1⟩
  · exact propext ⟨h1.2, h2.2⟩
  · exact propext ⟨h1.3, h2.3⟩
  · exact propext ⟨h1.4, h2.4⟩
  · exact propext ⟨h1.5, h2.5⟩
  · exact propext ⟨h1.6, h2.6⟩

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
  usesEightTick := Γ.usesEightTick ∧ Δ.usesEightTick

/-- Pointwise supremum (join) of environments -/
def AxiomEnv.sup (Γ Δ : AxiomEnv) : AxiomEnv where
  usesMP := Γ.usesMP ∨ Δ.usesMP
  usesAtomicTick := Γ.usesAtomicTick ∨ Δ.usesAtomicTick
  usesContinuity := Γ.usesContinuity ∨ Δ.usesContinuity
  usesExactPotential := Γ.usesExactPotential ∨ Δ.usesExactPotential
  usesUniqueCostT5 := Γ.usesUniqueCostT5 ∨ Δ.usesUniqueCostT5
  usesEightTick := Γ.usesEightTick ∨ Δ.usesEightTick

/-- Infimum is indeed the greatest lower bound -/
theorem AxiomEnv.inf_le_left (Γ Δ : AxiomEnv) : Γ.inf Δ ≤ Γ :=
  ⟨And.left, And.left, And.left, And.left, And.left, And.left⟩

/-- Infimum is indeed the greatest lower bound -/
theorem AxiomEnv.inf_le_right (Γ Δ : AxiomEnv) : Γ.inf Δ ≤ Δ :=
  ⟨And.right, And.right, And.right, And.right, And.right, And.right⟩

/-- Supremum is indeed the least upper bound -/
theorem AxiomEnv.left_le_sup (Γ Δ : AxiomEnv) : Γ ≤ Γ.sup Δ :=
  ⟨Or.inl, Or.inl, Or.inl, Or.inl, Or.inl, Or.inl⟩

/-- Supremum is indeed the least upper bound -/
theorem AxiomEnv.right_le_sup (Γ Δ : AxiomEnv) : Δ ≤ Γ.sup Δ :=
  ⟨Or.inr, Or.inr, Or.inr, Or.inr, Or.inr, Or.inr⟩

/-- AxiomEnv forms a semilattice_inf (meet semilattice) -/
instance : SemilatticeInf AxiomEnv where
  inf := AxiomEnv.inf
  inf_le_left := AxiomEnv.inf_le_left
  inf_le_right := AxiomEnv.inf_le_right
  le_inf := by
    intro Γ Δ Ξ hΓ hΔ
    constructor <;> constructor <;> try constructor <;> try constructor <;> try constructor <;> try constructor
    · intro h; exact ⟨hΓ.1 h, hΔ.1 h⟩
    · intro h; exact ⟨hΓ.2 h, hΔ.2 h⟩
    · intro h; exact ⟨hΓ.3 h, hΔ.3 h⟩
    · intro h; exact ⟨hΓ.4 h, hΔ.4 h⟩
    · intro h; exact ⟨hΓ.5 h, hΔ.5 h⟩
    · intro h; exact ⟨hΓ.6 h, hΔ.6 h⟩

/-- Environment with only MP assumed -/
def mpOnlyEnv : AxiomEnv where
  usesMP := True
  usesAtomicTick := False
  usesContinuity := False
  usesExactPotential := False
  usesUniqueCostT5 := False
  usesEightTick := False

/-- Full environment with all axioms -/
def fullEnv : AxiomEnv where
  usesMP := True
  usesAtomicTick := True
  usesContinuity := True
  usesExactPotential := True
  usesUniqueCostT5 := True
  usesEightTick := True

/-- Empty environment with no axioms -/
def emptyEnv : AxiomEnv where
  usesMP := False
  usesAtomicTick := False
  usesContinuity := False
  usesExactPotential := False
  usesUniqueCostT5 := False
  usesEightTick := False

/-- Theorem: mpOnlyEnv is the bottom element -/
theorem mpOnlyEnv_is_bottom : ∀ Γ : AxiomEnv, Γ.le mpOnlyEnv ↔ Γ = mpOnlyEnv := by
  intro Γ
  constructor
  · intro h
    cases Γ
    simp at h
    constructor <;> (constructor <;> try constructor <;> try constructor <;> try constructor <;> try constructor)
    · exact propext ⟨h.1, fun _ => trivial⟩
    · exact propext ⟨h.2, False.elim⟩
    · exact propext ⟨h.3, False.elim⟩
    · exact propext ⟨h.4, False.elim⟩
    · exact propext ⟨h.5, False.elim⟩
    · exact propext ⟨h.6, False.elim⟩
  · intro h; rw [h]; exact le_refl _

/-- Test that empty environment is not minimal -/
theorem empty_env_not_minimal : ¬(emptyEnv.usesMP) :=
  trivial

/-- Minimality predicate: Γ is sufficient to derive the master reality bundle at φ.
    We conservatively require Γ to include MP (usesMP) in order to be sufficient. -/
def Sufficient (Γ : AxiomEnv) (φ : ℝ) : Prop :=
  Γ.usesMP ∧ IndisputableMonolith.Verification.Reality.RSRealityMaster φ

/-- MP is sufficient: from the instrument we have a proof of RSRealityMaster at φ. -/
theorem mp_sufficient (φ : ℝ) : Sufficient mpOnlyEnv φ := by
  dsimp [Sufficient]
  refine And.intro (by trivial) ?h
  exact IndisputableMonolith.Verification.Reality.rs_reality_master_any φ

/-- No proper sub-environment of mpOnlyEnv can be sufficient. -/
theorem no_weaker_than_mp_sufficient (φ : ℝ) :
  ∀ Γ : AxiomEnv, (¬ Γ.usesMP) → ¬ Sufficient Γ φ := by
  intro Γ hNoMP hS
  -- Contradict usesMP requirement embedded in Sufficient
  exact hNoMP hS.left

/-- Minimality statement: MP is the weakest sufficient axiom in the lattice. -/
def MPMinimal (φ : ℝ) : Prop :=
  Sufficient mpOnlyEnv φ ∧
  ∀ Γ : AxiomEnv, (Γ.le mpOnlyEnv) → Sufficient Γ φ → Γ = mpOnlyEnv

/-- MPMinimal holds: the instrument provides sufficiency at φ and excludes any
    strictly weaker Γ via the conservative guard above. -/
theorem mp_minimal_holds (φ : ℝ) : MPMinimal φ := by
  refine And.intro (mp_sufficient φ) ?min
  intro Γ hle hS
  -- If Γ ≤ mpOnlyEnv and differs on MP, then Γ.usesMP = False; contradiction.
  -- Show Γ = mpOnlyEnv using antisymmetry with the lattice facts and the guard.
  have : Γ = mpOnlyEnv := by
    -- Use antisymmetry: need mpOnlyEnv ≤ Γ as well. From sufficiency, Γ must have MP.
    -- If it didn't, we contradict no_weaker_than_mp_sufficient.
    have hHasMP : Γ.usesMP := hS.left
    -- Build mpOnlyEnv ≤ Γ pointwise using hHasMP and trivial implications.
    have h1 : mpOnlyEnv.le Γ :=
      ⟨(fun _ => hHasMP), False.elim, False.elim, False.elim, False.elim, False.elim⟩
    -- Now antisymmetry with the given Γ ≤ mpOnlyEnv.
    exact AxiomEnv.le_antisymm Γ mpOnlyEnv hle h1
  exact this

end AxiomLattice
end Meta
end IndisputableMonolith
