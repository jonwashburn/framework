import Mathlib
import IndisputableMonolith.Token.WTokenId

/-!
# WToken candidate predicate + classification (parameter-level)

This file implements the **operational core** of WS2 (forced classification) at the
parameter level:

- define an explicit constraint predicate (`IsWTokenCandidateParam`) on raw parameters,
- package the constrained parameters as a type (`WTokenCandidateParam`),
- prove this type is **equivalent** to the canonical identity type `Token.WTokenId`,
  hence has exactly 20 inhabitants.

Claim hygiene:
- This is *not yet* a full “forced by RS from DFT atoms” proof. It is the clean,
  mechanized statement: **given the repo’s current parameter constraints**, there are
  exactly 20 legal token parameterizations, and they correspond 1:1 with `WTokenId`.
- The stronger, physics-facing “forcing” story (from dynamics/MDL/DFT) remains WS2 follow-up work.
-/

namespace IndisputableMonolith
namespace Token

open IndisputableMonolith.Water

/-! ## Candidate predicate on raw parameters -/

/-- Raw parameter triple (mode family, φ-level, τ-offset). -/
abbrev WTokenRawParams := Water.WTokenMode × Water.PhiLevel × Water.TauOffset

/-- RS legality predicate (current repo encoding):

- non-mode4 families must have τ-offset = τ0
- mode4 may have τ0 or τ2 (both allowed)

This matches the `tau_valid` field used by `Water.WTokenSpec`. -/
def IsWTokenCandidateParam (p : WTokenRawParams) : Prop :=
  let (mode, _phi, tau) := p
  mode ≠ Water.WTokenMode.mode4 → tau = Water.TauOffset.tau0

/-- The type of legal WToken parameterizations. -/
def WTokenCandidateParam : Type :=
  { p : WTokenRawParams // IsWTokenCandidateParam p }

namespace WTokenCandidateParam

/-- Convert candidate parameters into the existing `Water.WTokenSpec`. -/
def toWaterSpec (c : WTokenCandidateParam) : Water.WTokenSpec :=
  match c with
  | ⟨(mode, phi, tau), hp⟩ =>
      have hv : mode ≠ Water.WTokenMode.mode4 → tau = Water.TauOffset.tau0 := by
        simpa [IsWTokenCandidateParam] using hp
      ⟨mode, phi, tau, hv⟩

/-- Convert a `Water.WTokenSpec` into candidate parameters by forgetting the proof field. -/
def ofWaterSpec (w : Water.WTokenSpec) : WTokenCandidateParam :=
  ⟨(w.mode, w.phi_level, w.tau_offset), w.tau_valid⟩

@[simp] theorem ofWaterSpec_toWaterSpec (c : WTokenCandidateParam) :
    ofWaterSpec (toWaterSpec c) = c := by
  cases c with
  | mk p hp =>
    cases p with
    | mk mode rest =>
      cases rest with
      | mk phi tau =>
        -- Proof-irrelevance for the `Prop` field `IsWTokenCandidateParam`.
        apply Subtype.ext
        · rfl

/-- Proof-irrelevance helper for `Water.WTokenSpec` (Prop field). -/
private theorem mk_eq :
    ∀ (m : WTokenMode) (p : PhiLevel) (t : TauOffset)
      (h₁ h₂ : m ≠ WTokenMode.mode4 → t = TauOffset.tau0),
      (⟨m, p, t, h₁⟩ : Water.WTokenSpec) = ⟨m, p, t, h₂⟩ := by
  intro m p t h₁ h₂
  have : h₁ = h₂ := by
    apply Subsingleton.elim
  cases this
  rfl

@[simp] theorem toWaterSpec_ofWaterSpec (w : Water.WTokenSpec) :
    toWaterSpec (ofWaterSpec w) = w := by
  cases w with
  | mk mode phi tau hv =>
    -- only the Prop field differs; use proof irrelevance
    simp [toWaterSpec, ofWaterSpec]

/-- Equivalence: candidate params are exactly `Water.WTokenSpec`. -/
def equivWaterSpec : WTokenCandidateParam ≃ Water.WTokenSpec :=
{ toFun := toWaterSpec
, invFun := ofWaterSpec
, left_inv := by intro c; simp [ofWaterSpec_toWaterSpec]
, right_inv := by intro w; simp [toWaterSpec_ofWaterSpec]
}

/-- Equivalence: candidate params are exactly the canonical IDs. -/
def equivId : WTokenCandidateParam ≃ Token.WTokenId :=
  equivWaterSpec.trans (Token.WTokenId.equivSpec.symm)

noncomputable instance : Fintype WTokenCandidateParam :=
  Fintype.ofEquiv Token.WTokenId equivId.symm

theorem card_eq_20 : Fintype.card WTokenCandidateParam = 20 := by
  -- Transport along the equivalence to `WTokenId`.
  simpa using (Fintype.card_congr equivId)

end WTokenCandidateParam

end Token
end IndisputableMonolith
