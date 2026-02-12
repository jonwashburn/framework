import Mathlib
import IndisputableMonolith.Verification.Exclusivity

/-!
# RecognitionReality: minimal public API

This module provides a small, stable surface for downstream “reports” and certificates.
It is derived from `Verification.Exclusivity.ExclusiveRealityPlus` and exposes:

- a bundled witness at the uniquely pinned scale `φ`,
- noncomputable accessors for that witness, and
- a lightweight “ultimate closure” predicate + uniqueness theorem.
-/

namespace IndisputableMonolith
namespace Verification
namespace RecognitionReality

open Verification
open Verification.Exclusivity
open IndisputableMonolith.RH.RS

/-- Coherence predicate for canonical units classes at scale `φ` (Prop-level). -/
def UnitsClassCoherence (φ : ℝ) : Prop :=
  (∀ (F : ZeroParamFramework φ) (e : UnitsQuotCarrier F ≃ UnitsQuotCarrier F),
      e (canonicalUnitsClass φ F) = canonicalUnitsClass φ F)
  ∧
  (∀ (F G : ZeroParamFramework φ),
      (unitsQuot_equiv F G) (canonicalUnitsClass φ F) = canonicalUnitsClass φ G)

/-- At scale `φ`, package the master + definitional-uniqueness + bi-interpretability data. -/
structure RecognitionRealityAt (φ : ℝ) where
  master    : Reality.RSRealityMaster φ
  defUnique : DefinitionalUniqueness φ
  bi        : BiInterpretabilityAt φ

/-- Existence and uniqueness of the pinned scale together with the bundled witness. -/
theorem recognitionReality_exists_unique :
  ∃! φ : ℝ, PhiSelection φ ∧ RecognitionRealityAt φ := by
  classical
  -- `ExclusiveRealityPlus` is already an `∃! φ, ...` statement; we just repackage its witness.
  rcases exclusive_reality_plus_holds with ⟨phiStar, hPlus, huniq⟩
  rcases hPlus with ⟨hSel, hExclAt, hBi⟩
  refine ⟨phiStar, ?_, ?_⟩
  · refine ⟨hSel, ?_⟩
    exact { master := hExclAt.master, defUnique := hExclAt.defUnique, bi := hBi }
  · intro x hx
    have hxExclAt : ExclusivityAt x :=
      { master := hx.right.master, defUnique := hx.right.defUnique }
    have hxBi : BiInterpretabilityAt x := hx.right.bi
    exact huniq x ⟨hx.left, hxExclAt, hxBi⟩

/-! ### Public accessors (noncomputable choice) -/

noncomputable def recognitionReality_phi : ℝ :=
  Classical.choose (ExistsUnique.exists recognitionReality_exists_unique)

noncomputable def recognitionReality_at : RecognitionRealityAt recognitionReality_phi :=
  (Classical.choose_spec (ExistsUnique.exists recognitionReality_exists_unique)).right

noncomputable def recognitionReality_master : Reality.RSRealityMaster recognitionReality_phi :=
  (recognitionReality_at).master

noncomputable def recognitionReality_definitionalUniqueness :
    DefinitionalUniqueness recognitionReality_phi :=
  (recognitionReality_at).defUnique

noncomputable def recognitionReality_bi : BiInterpretabilityAt recognitionReality_phi :=
  (recognitionReality_at).bi

/-! ### Ultimate closure (lightweight) -/

/-- Ultimate closure at scale `φ`: the `ExclusiveRealityPlus` witness at `φ` together with
the canonical units-class coherence at `φ`. -/
def UltimateClosure (φ : ℝ) : Prop :=
  (PhiSelection φ ∧ ExclusivityAt φ ∧ BiInterpretabilityAt φ)
  ∧ UnitsClassCoherence φ

theorem ultimate_closure_holds : ∃! φ : ℝ, UltimateClosure φ := by
  classical
  rcases exclusive_reality_plus_holds with ⟨phiStar, hPlus, huniq⟩
  refine ⟨phiStar, ?_, ?_⟩
  · refine ⟨hPlus, ?_⟩
    -- `units_class_coherence` proves the conjunction packaged by `UnitsClassCoherence`.
    simpa [UnitsClassCoherence] using (units_class_coherence (φ := phiStar))
  · intro x hx
    exact huniq x hx.left

/-- The chosen pinned scale equals the canonical constant `Constants.phi` (by uniqueness). -/
lemma recognitionReality_phi_eq_constants :
  recognitionReality_phi = IndisputableMonolith.Constants.phi := by
  classical
  -- recognitionReality_phi satisfies PhiSelection by construction
  have hChosen :
      IndisputableMonolith.RH.RS.PhiSelection recognitionReality_phi :=
    (Classical.choose_spec (ExistsUnique.exists recognitionReality_exists_unique)).left
  have hPhi :
      IndisputableMonolith.RH.RS.PhiSelection IndisputableMonolith.Constants.phi := by
    refine And.intro ?_ ?_
    · simpa using IndisputableMonolith.PhiSupport.phi_squared
    · exact lt_trans (by norm_num : (0 : ℝ) < 1) IndisputableMonolith.Constants.one_lt_phi
  -- uniqueness of φ under PhiSelection alone
  exact (IndisputableMonolith.PhiSupport.phi_unique_pos_root recognitionReality_phi).mp hChosen

/-- #eval-friendly confirmation string for the pinned φ equality. -/
@[simp] noncomputable def recognition_phi_eq_constants_report : String :=
  if recognitionReality_phi = IndisputableMonolith.Constants.phi then
    "recognitionReality_phi = Constants.phi: OK"
  else
    "recognitionReality_phi = Constants.phi: FAILED"

end RecognitionReality
end Verification
end IndisputableMonolith
