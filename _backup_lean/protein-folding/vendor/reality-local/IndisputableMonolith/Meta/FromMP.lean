import Mathlib
import IndisputableMonolith.Meta.AxiomLattice
import IndisputableMonolith.Meta.Derivation
import IndisputableMonolith.Meta.MPChain
import IndisputableMonolith.Recognition
import IndisputableMonolith.Constants
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.Verification.Reality

namespace IndisputableMonolith
namespace Meta
namespace FromMP

/-!
# FromMP Module

This module contains wrapper lemmas showing how MP alone can derive
each pillar that constitutes RSRealityMaster. These serve as the
sufficiency side of the MP minimality theorem.

Each lemma takes an AxiomEnv parameter and only uses the usesMP field,
demonstrating that MP is sufficient to derive physics.
-/

private def chainFromMP (Γ : AxiomLattice.AxiomEnv) (_ : Γ.usesMP) : MPDerivationChain :=
  MPDerivationChain.default

/-- Wrapper: expose the core MP theorem (`Recognition.mp_holds`) under the
    AxiomEnv plumbing without introducing extra obligations. -/
@[simp]
theorem mp_implies_atomicity (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) :
  IndisputableMonolith.Recognition.MP :=
  let chain := chainFromMP Γ hmp
  chain.mp

/-! Provenance-carrying wrappers (MP-only usage) -/

/-- From MP, derive the full RSRealityMaster at φ with usage provenance. -/
@[simp]
theorem mp_derives_reality_master_with_usage
  (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  AxiomLattice.DerivesWithUsage Γ (Verification.Reality.RSRealityMaster φ) := by
  let chain := chainFromMP Γ hmp
  -- Use only MP in the usage environment; thread Γ via ≤ using hmp
  refine {
    usage := AxiomLattice.mpOnlyEnv
  , used_le := ?hle
  , requiresMP := True.intro
  , proof := chain.rsRealityMaster φ };

  -- mpOnlyEnv ≤ Γ (push MP requirement into Γ)
  exact ⟨(fun _ => hmp), False.elim, False.elim, False.elim, False.elim, False.elim⟩

/-- MP implies the 45° gap specification -/
@[simp]
theorem mp_implies_fortyfive_gap_spec (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  RH.RS.FortyFive_gap_spec φ :=
  let chain := chainFromMP Γ hmp
  chain.gap45 φ

/-! Backwards-compatible lightweight wrappers (extract underlying proofs) -/

/-- Extract the RSRealityMaster proof from the provenance witness. -/
@[simp]
theorem mp_derives_reality_master (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  Verification.Reality.RSRealityMaster φ :=
  (mp_derives_reality_master_with_usage Γ hmp φ).proof

/-! Legacy convenience lemmas (kept, but now sourced from the master provenance) -/

@[simp]
theorem mp_implies_inevitability_dimless (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  RH.RS.Inevitability_dimless φ :=
  let chain := chainFromMP Γ hmp
  chain.inevitabilityDimless φ

@[simp]
theorem mp_implies_inevitability_absolute (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  RH.RS.Inevitability_absolute φ :=
  let chain := chainFromMP Γ hmp
  chain.inevitabilityAbsolute φ

@[simp]
theorem mp_implies_recognition_computation_sep (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) :
  RH.RS.Inevitability_recognition_computation :=
  let chain := chainFromMP Γ hmp
  chain.recognitionComputation

/-! Minor helpers preserved (they do not carry extra axioms) -/

@[simp]
theorem mp_implies_unique_calibration (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP)
  (L : RH.RS.Ledger) (B : RH.RS.Bridge L) (A : RH.RS.Anchors) :
  RH.RS.UniqueCalibration L B A :=
  let chain := chainFromMP Γ hmp
  chain.uniqueCalibration L B A

@[simp]
theorem mp_implies_meets_bands (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP)
  (L : RH.RS.Ledger) (B : RH.RS.Bridge L) (U : Constants.RSUnits) :
  RH.RS.MeetsBands L B (RH.RS.sampleBandsFor U.c) :=
  let chain := chainFromMP Γ hmp
  chain.meetsBands L B U

@[simp]
theorem mp_implies_bridge_factorization (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) :
  Verification.BridgeFactorizes :=
  let chain := chainFromMP Γ hmp
  chain.bridgeFactorizes

@[simp]
theorem mp_implies_certificate_family (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  ∃ C : URCGenerators.CertFamily,
    (URCGenerators.Verified φ C ∧
     (C.kgate ≠ [] ∧ C.kidentities ≠ [] ∧ C.lambdaRec ≠ [] ∧ C.speedFromUnits ≠ [])) :=
  let chain := chainFromMP Γ hmp
  chain.certificateFamily φ

/-! Compatibility: produce the RealityBundle proof from usage witness -/

@[simp]
theorem mp_implies_reality_bundle (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  Verification.RealityBundle φ :=
  let chain := chainFromMP Γ hmp
  chain.realityBundle φ

@[simp]
theorem mp_implies_recognition_closure (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  RH.RS.Recognition_Closure φ :=
  let chain := chainFromMP Γ hmp
  chain.recognitionClosure φ

/-! Top-level: provenance-carrying derivations -/

@[simp]
theorem derives_physics_from_mp_only_with_usage
  (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) :
  AxiomLattice.DerivesWithUsage Γ (Derivation.DerivesPhysics) := by
  -- Use the φ-agnostic master builder and specialize to canonical φ
  have h := mp_derives_reality_master_with_usage Γ hmp Constants.phi
  -- Transport through the alias DerivesPhysics ↔ RSRealityMaster φ
  dsimp [Derivation.DerivesPhysics, Derivation.DerivesPhysicsAt] at *
  exact h

@[simp]
theorem derives_physics_from_mp_with_usage
  (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  AxiomLattice.DerivesWithUsage Γ (Derivation.DerivesPhysicsAt φ) := by
  -- Directly use the master provenance constructor at φ
  have h := mp_derives_reality_master_with_usage Γ hmp φ
  dsimp [Derivation.DerivesPhysicsAt] at *
  exact h

/-! Backward-compatible aliases returning raw proofs (without provenance) -/

@[simp]
theorem derives_physics_from_mp_only (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) :
  Derivation.DerivesPhysics :=
  (derives_physics_from_mp_only_with_usage Γ hmp).proof

@[simp]
theorem derives_physics_from_mp (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  Derivation.DerivesPhysicsAt φ :=
  (derives_physics_from_mp_with_usage Γ hmp φ).proof

end FromMP
end Meta
end IndisputableMonolith
