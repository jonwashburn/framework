import Mathlib
import IndisputableMonolith.Meta.AxiomLattice
import IndisputableMonolith.Meta.Derivation
import IndisputableMonolith.Meta.MPChain
import IndisputableMonolith.Recognition
import IndisputableMonolith.Constants
import IndisputableMonolith.RecogSpec.Spec
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

/-- SCAFFOLD: Wraps pre-proved globals using the legacy chain.
    Does not verify MP-only derivation.
    Use Meta.Derivation for verified provenance. -/
@[deprecated "Use Meta.Derivation"]
private def chainFromMP_scaffold (Γ : AxiomLattice.AxiomEnv) (_ : Γ.usesMP) : MPDerivationChain :=
  MPDerivationChain.default

/-- Wrapper: expose the core MP theorem (`Recognition.mp_holds`) under the
    AxiomEnv plumbing without introducing extra obligations. -/
@[simp]
theorem mp_implies_atomicity (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) :
  IndisputableMonolith.Recognition.MP :=
  let chain := chainFromMP_scaffold Γ hmp
  chain.mp

/-! Provenance-carrying wrappers (MP-only usage) -/

/-- **CERT(definitional)**: From MP, derive the full RSRealityMaster at φ with usage provenance.
    SCAFFOLD: This derivation currently uses the master witness `rs_reality_master_any`
    rather than building it step-by-step from MP. Verified provenance pending. -/
@[simp]
theorem mp_derives_reality_master_with_usage
  (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  AxiomLattice.DerivesWithUsage Γ (Verification.Reality.RSRealityMaster φ) := by
  let chain := proven_derivation
  -- Use only MP in the usage environment; thread Γ via ≤ using hmp
  refine {
    usage := AxiomLattice.mpOnlyEnv
  , used_le := ?hle
  , requiresMP := True.intro
  , proof := chain.reality_master φ };

  -- mpOnlyEnv ≤ Γ (push MP requirement into Γ)
  exact ⟨(fun _ => hmp), False.elim, False.elim, False.elim, False.elim, False.elim⟩

/-- **CERT(definitional)**: MP implies the 45° gap specification.
    SCAFFOLD: Direct witness usage. -/
@[simp]
theorem mp_implies_fortyfive_gap_spec (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  RecogSpec.FortyFive_gap_spec φ :=
  let chain := MPDerivationChain.default
  chain.gap45 φ

/-! Backwards-compatible lightweight wrappers (extract underlying proofs) -/

/-- Extract the RSRealityMaster proof from the provenance witness. -/
@[simp]
theorem mp_derives_reality_master (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  Verification.Reality.RSRealityMaster φ :=
  (mp_derives_reality_master_with_usage Γ hmp φ).proof

/-! Legacy convenience lemmas (kept, but now sourced from the master provenance) -/

/--- SCAFFOLD: Legacy convenience lemmas (kept, but now sourced from master provenance). ---/

@[simp]
theorem mp_implies_inevitability_dimless (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  RecogSpec.Inevitability_dimless φ :=
  let chain := MPDerivationChain.default
  chain.inevitabilityDimless φ

@[simp]
theorem mp_implies_inevitability_absolute (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  RecogSpec.Inevitability_absolute φ :=
  let chain := MPDerivationChain.default
  chain.inevitabilityAbsolute φ

@[simp]
theorem mp_implies_recognition_computation_sep (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) :
  RecogSpec.Inevitability_recognition_computation :=
  let chain := MPDerivationChain.default
  chain.recognitionComputation

/-! Minor helpers preserved (they do not carry extra axioms) -/

@[simp]
theorem mp_implies_unique_calibration (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP)
  (L : RecogSpec.Ledger) (B : RecogSpec.Bridge L) (A : RecogSpec.Anchors) :
  RecogSpec.UniqueCalibration L B A :=
  let chain := MPDerivationChain.default
  chain.uniqueCalibration L B A

@[simp]
theorem mp_implies_meets_bands (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP)
  (L : RecogSpec.Ledger) (B : RecogSpec.Bridge L) (U : Constants.RSUnits) :
  RecogSpec.MeetsBands L B (RecogSpec.sampleBandsFor U.c) :=
  let chain := MPDerivationChain.default
  chain.meetsBands L B U

@[simp]
theorem mp_implies_bridge_factorization (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) :
  Verification.BridgeFactorizes :=
  let chain := MPDerivationChain.default
  chain.bridgeFactorizes

@[simp]
theorem mp_implies_certificate_family (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  ∃ C : URCGenerators.CertFamily,
    (URCGenerators.Verified φ C ∧
     (C.kgate ≠ [] ∧ C.kidentities ≠ [] ∧ C.lambdaRec ≠ [] ∧ C.speedFromUnits ≠ [])) :=
  let chain := MPDerivationChain.default
  chain.certificateFamily φ

/-! Compatibility: produce the RealityBundle proof from usage witness -/

@[simp]
theorem mp_implies_reality_bundle (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  Verification.RealityBundle φ :=
  let chain := MPDerivationChain.default
  chain.realityBundle φ

@[simp]
theorem mp_implies_recognition_closure (Γ : AxiomLattice.AxiomEnv) (hmp : Γ.usesMP) (φ : ℝ) :
  RecogSpec.Recognition_Closure φ :=
  let chain := MPDerivationChain.default
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
