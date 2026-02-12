import IndisputableMonolith.Verification.MeaningPeriodicTable.Spec
import IndisputableMonolith.Foundation.WTokenReference

/-!
# Mode+Φ Forcing Closure

This module combines two independently forced components of the RS/ULL semantic signature:

1. **Mode family** (DFT basis class) is forced by the deterministic classifier
   in `Verification/MeaningPeriodicTable/Spec.lean`.
2. **φ-level** is forced by the RS mismatch-cost argmin over the finite set of φ-levels
   (`Foundation/WTokenReference.projectOntoPhiLattice` and its minimizer theorem).

The output is a *partial* signature `(modeFamily, phiLevel)`.  τ-variant / gauge data
is deliberately excluded here and handled in a later closure step.
-/

namespace IndisputableMonolith
namespace Verification
namespace MeaningPeriodicTable

open scoped Classical

/-! ## Canonical “partial signature” type -/

structure ModePhiSignature where
  modeFamily : Water.WTokenMode
  phiLevel : Water.PhiLevel
  deriving Repr

/-! ## Bridge maps between Foundation φ-levels and Water φ-levels -/

def waterPhiLevelOfRef : Foundation.ReferenceWToken.PhiLevel → Water.PhiLevel
  | .level0 => .level0
  | .level1 => .level1
  | .level2 => .level2
  | .level3 => .level3

def refPhiLevelOfWater : Water.PhiLevel → Foundation.ReferenceWToken.PhiLevel
  | .level0 => .level0
  | .level1 => .level1
  | .level2 => .level2
  | .level3 => .level3

@[simp] lemma water_ref_roundtrip (p : Water.PhiLevel) :
    waterPhiLevelOfRef (refPhiLevelOfWater p) = p := by
  cases p <;> rfl

@[simp] lemma ref_water_roundtrip (p : Foundation.ReferenceWToken.PhiLevel) :
    refPhiLevelOfWater (waterPhiLevelOfRef p) = p := by
  cases p <;> rfl

/-! ## Mode-family extraction from the classifier -/

def modeOfBasisClass : BasisClass → Water.WTokenMode
  | .mode1_7 => .mode1_7
  | .mode2_6 => .mode2_6
  | .mode3_5 => .mode3_5
  | .mode4   => .mode4

lemma modeOfBasisClass_basisClassOf (w : CanonicalTokenId) :
    modeOfBasisClass (basisClassOf w) = (Token.WTokenId.toSpec w).mode := by
  -- `basisClassOf` is defined by case-splitting on the token's `mode`.
  cases hm : (Token.WTokenId.toSpec w).mode <;>
    simp [basisClassOf, modeOfBasisClass, hm]

noncomputable def forcedModeFamily (v : Fin 8 → ℂ) : Option Water.WTokenMode :=
  match classify v with
  | .exact w => some (modeOfBasisClass (basisClassOf w))
  | .ambiguous => none
  | .invalid => none

/-! ## φ-level forcing from RS cost argmin -/

noncomputable def forcedPhiLevel (r : ℝ) (hr : 0 < r) : Water.PhiLevel :=
  waterPhiLevelOfRef (Foundation.WTokenReference.projectOntoPhiLattice r hr)

@[simp] theorem refPhiLevelOfWater_forcedPhiLevel (r : ℝ) (hr : 0 < r) :
    refPhiLevelOfWater (forcedPhiLevel r hr) = Foundation.WTokenReference.projectOntoPhiLattice r hr := by
  -- unfold and use the roundtrip lemma
  simp [forcedPhiLevel]

theorem forcedPhiLevel_minimizes_reference (r : ℝ) (hr : 0 < r) :
    ∀ level : Foundation.ReferenceWToken.PhiLevel,
      Cost.Jcost
          (r / Constants.phi ^
              (Foundation.WTokenReference.phiLevelExponent (refPhiLevelOfWater (forcedPhiLevel r hr)) : ℝ))
        ≤
      Cost.Jcost
          (r / Constants.phi ^
              (Foundation.WTokenReference.phiLevelExponent level : ℝ)) := by
  intro level
  -- reduce to the existing theorem
  simpa [refPhiLevelOfWater_forcedPhiLevel] using
    (Foundation.WTokenReference.projection_minimizes_reference r hr level)

/-! ## Combined forcing: (mode family, φ-level) -/

noncomputable def forcedModePhiSignature (v : Fin 8 → ℂ) (r : ℝ) (hr : 0 < r) : Option ModePhiSignature :=
  match forcedModeFamily v with
  | none => none
  | some m => some ⟨m, forcedPhiLevel r hr⟩

/-! ## Correctness on canonical bases (mode-family half) -/

theorem forcedModeFamily_basisOfId (w : CanonicalTokenId) :
    forcedModeFamily (Token.WTokenId.basisOfId w) =
      some (modeOfBasisClass (basisClassOf w)) := by
  -- Use the existing theorem: classify(basisOfId w) = exact w' for some w' in the same basis class.
  rcases classify_returns_exact_same_class w with ⟨w', hw'class, hw'classify⟩
  -- Reduce.
  simp [forcedModeFamily, hw'classify, hw'class]

theorem forcedModePhiSignature_basisOfId (w : CanonicalTokenId) (r : ℝ) (hr : 0 < r) :
    forcedModePhiSignature (Token.WTokenId.basisOfId w) r hr =
      some ⟨modeOfBasisClass (basisClassOf w), forcedPhiLevel r hr⟩ := by
  simp [forcedModePhiSignature, forcedModeFamily_basisOfId, hr]

end MeaningPeriodicTable
end Verification
end IndisputableMonolith
