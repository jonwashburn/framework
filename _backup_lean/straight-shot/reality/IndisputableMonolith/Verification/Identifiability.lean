import Mathlib
import IndisputableMonolith.RecogSpec.Framework
import IndisputableMonolith.Verification.Identifiability.Observations
import IndisputableMonolith.Verification.Identifiability.Costs
import IndisputableMonolith.Verification.Identifiability.StrictMinimality
import IndisputableMonolith.Verification.Exclusivity

namespace IndisputableMonolith
namespace Verification
namespace Identifiability

open IndisputableMonolith
open IndisputableMonolith.RecogSpec
open IndisputableMonolith.Verification

/-! ### Faithfulness and identifiability orchestrations -/

/-- Faithfulness: observational equality produces the strengthened definitional witness,
    simultaneously relating the units quotients and supplying canonical bridge
    interpretations into the explicit universal target (no global uniqueness needed). -/
theorem faithfulness
    {φ : ℝ} (F G : ZeroParamFramework φ) (hObs : ObsEqual φ F G) :
    Exclusivity.DefinitionalEquivalence φ F G := by
  -- Classical reasoning is confined to the Exclusivity layer; this theorem
  -- only orchestrates existing fenced lemmas.
  rcases zpf_isomorphic F G with ⟨unitsIso⟩
  have hFobs := Exclusivity.canonicalInterpretation_observe_eq (φ:=φ) (F:=F)
  have hGobs := Exclusivity.canonicalInterpretation_observe_eq (φ:=φ) (F:=G)
  have hFpack := Exclusivity.BridgeInterpretation.observedFromPack_explicit_eq_ud
    (φ:=φ) (F:=F) (Exclusivity.canonicalInterpretation φ F)
  have hGpack := Exclusivity.BridgeInterpretation.observedFromPack_explicit_eq_ud
    (φ:=φ) (F:=G) (Exclusivity.canonicalInterpretation φ G)
  have hOneG : OnePoint (UnitsQuotCarrier G) := zpf_unitsQuot_onePoint G
  exact
    ⟨
      ⟨
        hObs
      , unitsIso
      , by exact hOneG _ _
      , Exclusivity.canonicalInterpretation φ F
      , Exclusivity.canonicalInterpretation φ G
      , hFobs.trans hFpack.symm
      , hGobs.trans hGpack.symm
      , hFpack.trans hGpack.symm
      ⟩
    ⟩

/-! ### Strict minimality tightening -/

lemma strict_minimality_forces_ud
    {φ : ℝ} (F G : ZeroParamFramework φ)
    (hObs : ObsEqual φ F G)
    (hFmin : StrictMinimal φ F) (hGmin : StrictMinimal φ G) :
    observe φ F = observedFromUD φ (UD_explicit φ) ∧
    observe φ G = observedFromUD φ (UD_explicit φ) :=
  strict_minimality_observe_eq_ud (φ:=φ) hFmin hGmin hObs

lemma strict_minimality_units_witness
    {φ : ℝ} (F G : ZeroParamFramework φ)
    (hObs : ObsEqual φ F G)
    (hFmin : StrictMinimal φ F) (hGmin : StrictMinimal φ G) :
    Exclusivity.DefinitionalWitness φ F G := by
  have hObsUD := strict_minimality_forces_ud (φ:=φ) F G hObs hFmin hGmin
  rcases hObsUD with ⟨hFobs, hGobs⟩
  rcases zpf_isomorphic F G with ⟨unitsIso⟩
  set interpF := Exclusivity.canonicalInterpretation φ F
  set interpG := Exclusivity.canonicalInterpretation φ G
  have hFpack := Exclusivity.BridgeInterpretation.observedFromPack_explicit_eq_ud
    (φ:=φ) (F:=F) interpF
  have hGpack := Exclusivity.BridgeInterpretation.observedFromPack_explicit_eq_ud
    (φ:=φ) (F:=G) interpG
  refine
  {
    obsEqual := by
      simpa [ObsEqual, hFobs, hGobs]
    , unitsIso := unitsIso
  , unitsCanonical := by
      simpa using
        Exclusivity.canonicalInterpretation_matches_ud_unique_units
          (φ:=φ) (F:=F)
          (B':=interpF.bridge)
          (Exclusivity.canonicalInterpretation_matches_ud_eval (φ:=φ) (F:=F))
    , interpF := interpF
    , interpG := interpG
    , obsF := hFobs.trans hFpack.symm
    , obsG := hGobs.trans hGpack.symm
    , obsShared := hFpack.trans hGpack.symm
  }

/-- Observational equality with strict minimality forces the canonical interpretation data
    and hence supplies the strengthened definitional witness. -/
theorem obs_equal_implies_definitional
    {φ : ℝ} (F G : ZeroParamFramework φ)
    (hObs : ObsEqual φ F G)
    (hFmin : StrictMinimal φ F) (hGmin : StrictMinimal φ G) :
    Exclusivity.DefinitionalEquivalence φ F G := by
  exact ⟨strict_minimality_units_witness (φ:=φ) F G hObs hFmin hGmin⟩

/-- Identifiability at scale φ: observational equality together with strict
    minimality yields definitional equivalence. The strict minimality witnesses
    are retained to emphasise the intended strengthening (cost rigour), even
    though faithfulness already provides the definitional witness. -/
theorem identifiable_at
  {φ : ℝ} (F G : ZeroParamFramework φ)
  (hObs : ObsEqual φ F G)
  (hFmin : StrictMinimal φ F) (hGmin : StrictMinimal φ G) :
    Exclusivity.DefinitionalEquivalence φ F G :=
  obs_equal_implies_definitional (φ:=φ) F G hObs hFmin hGmin

/-- At scale φ, the class is identifiable under the skeleton assumptions. -/
def IdentifiableAt (φ : ℝ) : Prop :=
  ∀ F G : ZeroParamFramework φ,
    ObsEqual φ F G → StrictMinimal φ F → StrictMinimal φ G →
      Exclusivity.DefinitionalEquivalence φ F G

theorem identifiable_at_any (φ : ℝ) : IdentifiableAt φ := by
  intro F G hObs hF hG
  exact identifiable_at F G hObs hF hG

end Identifiability
end Verification
end IndisputableMonolith
