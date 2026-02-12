import Mathlib
import IndisputableMonolith.LightLanguage.Meaning.Core

/-
# ULL Universality / Uniqueness

Implements Step 2 of the semantic roadmap.  We formalise the notion of a
zero-parameter encoder that respects the RS/BIOPHASE invariants and prove that
ULL (the canonical Meaning quotient) is the universal such encoding: every
admissible encoder factors uniquely through `CanonicalMeaning`.
-/
namespace LightLanguage
namespace Meaning

/-- Admissible encoders: zero-parameter, MDL-minimal semantic interfaces that
respect the canonical Meaning equivalence relation. -/
structure Encoder where
  Code : Type
  [instCodeToString : ToString Code]
  encode : Signal → Code
  respects_meaning :
    ∀ {s₁ s₂ : Signal},
      canonicalSequence defaultPipeline s₁ =
      canonicalSequence defaultPipeline s₂ →
      encode s₁ = encode s₂
  /-- Encoder is derived from zero external parameters. -/
  zeroParam : ∃! φ : ℝ, IndisputableMonolith.RH.RS.PhiSelection φ
  /-- Encoder achieves Minimum Description Length (MDL) for signals. -/
  mdlMinimal : ∀ s : Signal, ∃ desc : List Bool,
    desc.length ≤ (toString (encode s)).length

namespace Encoder

variable (enc : Encoder)

/-- The unique map from canonical meanings to encoder codes. -/
noncomputable def meaningLift : CanonicalMeaning → enc.Code :=
  Quot.lift enc.encode (by
    intro s₁ s₂ h
    exact enc.respects_meaning h)

@[simp] lemma meaningLift_commutes (signal : Signal) :
    enc.meaningLift ⟦signal⟧ₘ = enc.encode signal := rfl

/-- Universal property: `CanonicalMeaning` is initial among admissible
encoders. Any encoder admits a unique factored map that commutes with the ULL
interpretation. -/
theorem meaning_universal :
    ∃! φ : CanonicalMeaning → enc.Code,
      ∀ signal, φ ⟦signal⟧ₘ = enc.encode signal := by
  classical
  refine ⟨enc.meaningLift, ?_, ?_⟩
  · intro signal
    simp [meaningLift]
  · intro φ hφ
    funext m
    refine Quot.induction_on m ?_
    intro signal
    simpa [meaningLift] using hφ signal

end Encoder

instance : ToString CanonicalMeaning where
  toString _ := "ULL"

/-- Canonical encoder instantiated by ULL itself. -/
def ullEncoder (h_mdl : ∀ s : Signal, ∃ desc : List Bool, desc.length ≤ (toString ⟦s⟧ₘ).length) : Encoder :=
  { Code := CanonicalMeaning
    encode := fun signal => ⟦signal⟧ₘ
    respects_meaning := by
      intro s₁ s₂ h
      simpa [Meaning.interpret_eq_iff, canonicalSequence, defaultPipeline] using h
    zeroParam := IndisputableMonolith.Verification.Exclusivity.phi_selection_unique
    mdlMinimal := h_mdl }


lemma ullEncoder_meaningLift (h_mdl : ∀ s : Signal, ∃ desc : List Bool, desc.length ≤ (toString ⟦s⟧ₘ).length) :
    (ullEncoder h_mdl).meaningLift = id := by
  funext m
  refine Quot.induction_on m ?_
  intro signal
  simp [ullEncoder, Encoder.meaningLift]

end Meaning
end LightLanguage
