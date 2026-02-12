import Mathlib
import IndisputableMonolith.Verification.Reality
import IndisputableMonolith.Verification.Identifiability.StrictMinimality

/-!
# Bi-Interpretability Layer

Forward and reverse reconstruction results for zero-parameter frameworks at scale `φ`.

`BiInterpretability φ` collects:
* forward reconstruction (`observe` equals the canonical explicit pack)
* reverse reconstruction (`observe` collapses to the canonical universal ledger)
* matching of the canonical bridge against the explicit universal data
* strict minimality witness
* zero-cost witness

`RecognitionReality φ` extends the master `Reality` bundle with the collection above.

Remaining future work (tracked elsewhere): bridge symmetry coherence, categorical
equivalence, and dual-agent alignment.
-/

namespace IndisputableMonolith
namespace Verification
namespace BiInterpretability

open Verification
open Verification.Identifiability
open Identifiability

variable (φ : ℝ)

/-- Forward reconstruction: every zero-parameter framework reproduces its observed ledger
via the canonical explicit pack. -/
def ForwardReconstruction : Prop :=
  ∀ F : ZeroParamFramework φ,
    observe φ F = observedFromPack φ (P := (canonicalInterpretation φ F).packExplicit)

/-- Reverse reconstruction: every zero-parameter framework observes the universal target. -/
def ReverseReconstruction : Prop :=
  ∀ F : ZeroParamFramework φ,
    observe φ F = observedFromUD φ (UD_explicit φ)

/-- Bi-interpretability bundle: forward/reverse reconstruction and supporting witnesses. -/
structure BiInterpretability (φ : ℝ) : Prop where
  forward : ForwardReconstruction φ
  reverse : ReverseReconstruction φ
  canonical_bridge :
    ∀ F : ZeroParamFramework φ,
      RH.RS.MatchesEval φ F.L (canonicalInterpretation φ F).bridge (UD_explicit φ)
  strict_minimal :
    ∀ F : ZeroParamFramework φ, StrictMinimal φ F
  zero_cost :
    ∀ F : ZeroParamFramework φ, costOf φ F = 0

/-- RecognitionReality combines the master reality bundle with bi-interpretability. -/
def RecognitionReality (φ : ℝ) : Prop :=
  Reality.RSRealityMaster φ ∧ BiInterpretability φ

namespace Lemmas

variable {φ}

lemma forward_holds (φ : ℝ) : ForwardReconstruction φ := by
  intro F
  simpa using (canonicalInterpretation_observe_eq (φ := φ) F)

lemma reverse_holds (φ : ℝ) : ReverseReconstruction φ := by
  intro F
  simpa using (observe_eq_ud (φ := φ) F)

lemma canonical_bridge_holds (φ : ℝ) :
    ∀ F : ZeroParamFramework φ,
      RH.RS.MatchesEval φ F.L (canonicalInterpretation φ F).bridge (UD_explicit φ) := by
  intro F
  simpa using (canonicalInterpretation_matches_ud_eval (φ := φ) F)

lemma strict_minimal_holds (φ : ℝ) :
    ∀ F : ZeroParamFramework φ, StrictMinimal φ F :=
  fun F => strict_minimality_default (φ := φ) F

lemma zero_cost_holds (φ : ℝ) :
    ∀ F : ZeroParamFramework φ, costOf φ F = 0 :=
  fun F => costOf_eq_zero (φ := φ) F

lemma biInterpretability_any (φ : ℝ) : BiInterpretability φ :=
{ forward := forward_holds (φ := φ)
, reverse := reverse_holds (φ := φ)
, canonical_bridge := canonical_bridge_holds (φ := φ)
, strict_minimal := strict_minimal_holds (φ := φ)
, zero_cost := zero_cost_holds (φ := φ) }

lemma recognitionReality_any (φ : ℝ) : RecognitionReality φ := by
  refine And.intro ?master (biInterpretability_any (φ := φ))
  exact Reality.rs_reality_master_any φ

end Lemmas

export Lemmas (forward_holds reverse_holds canonical_bridge_holds
  strict_minimal_holds zero_cost_holds biInterpretability_any recognitionReality_any)

end BiInterpretability
end Verification
end IndisputableMonolith
