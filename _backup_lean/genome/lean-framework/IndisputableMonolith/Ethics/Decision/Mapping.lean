import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Decision

def mapReqMicro (r : Request A) (φ : Alignment.Morph) : Request A :=
  { r with micro := r.micro.map (fun m => Alignment.mapMicro m φ) }

@[simp] lemma truthOk_mapped (P : Policy A) (r : Request A) (φ : Alignment.Morph) :
  truthOk (P:=P) (mapReqMicro r φ) = truthOk (P:=P) r := by
  unfold truthOk mapReqMicro
  cases P.truthContradicts? <;> simp

@[simp] lemma chooseTruthful_mapped (P : Policy A) (xs : List (Request A)) (φ : Alignment.Morph) :
  (chooseTruthful (P:=P) (xs.map (fun r => mapReqMicro r φ))) =
  (chooseTruthful (P:=P) xs).map (fun r => mapReqMicro r φ) := by
  classical
  unfold chooseTruthful
  cases P.evidence? with
  | none => simp [filterByGatesWithParity]
  | some E =>
      cases xs with
      | nil => simp
      | cons y yt => simp [filterByGatesWithParity]

@[simp] lemma consentOk_mapped (P : Policy A) (r : Request A) (φ : Alignment.Morph) :
  consentOk (P:=P) (mapReqMicro r φ) = consentOk (P:=P) r := by
  unfold consentOk mapReqMicro
  cases P.consent? <;> simp

@[simp] lemma harmOk_mapped (P : Policy A) (r : Request A) (φ : Alignment.Morph) :
  harmOk (P:=P) (mapReqMicro r φ) = harmOk (P:=P) r := by
  unfold harmOk mapReqMicro
  cases P.harmModel? <;> cases P.harmTol? <;> simp

@[simp] lemma deonticOk_mapped (P : Policy A) (r : Request A) (φ : Alignment.Morph) :
  deonticOk (P:=P) (mapReqMicro r φ) = deonticOk (P:=P) r := by
  unfold deonticOk mapReqMicro; simp

@[simp] lemma privacyOk_mapped (P : Policy A) (r : Request A) (φ : Alignment.Morph) :
  privacyOk (P:=P) (mapReqMicro r φ) = privacyOk (P:=P) r := by
  unfold privacyOk mapReqMicro
  cases P.privacyBudget? <;> cases P.privacyCost? <;> simp

@[simp] lemma coiOk_mapped (P : Policy A) (r : Request A) (φ : Alignment.Morph) :
  coiOk (P:=P) (mapReqMicro r φ) = coiOk (P:=P) r := by
  unfold coiOk mapReqMicro
  cases P.coi? <;> cases P.stakeGraph? <;> cases r.micro <;> cases P.sigma? <;> simp [Alignment.mapMicro]

@[simp] lemma robustOk_mapped (P : Policy A) (r : Request A) (φ : Alignment.Morph) :
  robustOk (P:=P) (mapReqMicro r φ) = robustOk (P:=P) r := by
  unfold robustOk mapReqMicro
  cases P.confidence? <;> cases P.minConfidence? <;> cases P.confInterval? <;> simp

end Decision
end Ethics
end IndisputableMonolith

