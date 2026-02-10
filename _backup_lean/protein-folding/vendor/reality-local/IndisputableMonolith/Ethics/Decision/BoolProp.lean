import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Decision

universe u
variable {A : Type u}

-- Prop-level counterparts (tied to existing structures; minimal semantics)
def JusticeOKP (r : Request A) : Prop := r.delta = 1 ∨ r.delta = -1
def ReciprocityOKP (r : Request A) : Prop := r.accurate = true
def TemperanceOKP (r : Request A) : Prop := r.delta ≠ 0
def WithinWindowP (r : Request A) : Prop := r.phase.val < 8
def UniqueInWindowP (r : Request A) : Prop := uniqueInWindow r = true
def FairnessOKP (r : Request A) : Prop := r.cq.coherence8 ≥ 0
def AdversarialOKP (r : Request A) : Prop := adversarialOk r = true
def TruthOKP (P : Policy A) (r : Request A) : Prop := truthOk (P:=P) r = true
def ConsentOKP (P : Policy A) (r : Request A) : Prop := consentOk (P:=P) r = true
def HarmOKP (P : Policy A) (r : Request A) : Prop := harmOk (P:=P) r = true
def DeonticOKP (P : Policy A) (r : Request A) : Prop := deonticOk (P:=P) r = true
def PrivacyOKP (P : Policy A) (r : Request A) : Prop := privacyOk (P:=P) r = true
def COIOKP (P : Policy A) (r : Request A) : Prop := coiOk (P:=P) r = true
def RobustOKP (P : Policy A) (r : Request A) : Prop := robustOk (P:=P) r = true
def FairnessBatchOKP (P : Policy A) (xs : List (Request A)) : Prop :=
  ∀ r ∈ xs, FairnessOKP r

-- Bool ↔ Prop bridging lemmas
@[simp] lemma justiceOk_true_iff (r : Request A) : justiceOk r = true ↔ JusticeOKP r := by
  simp [justiceOk, JusticeOKP]

@[simp] lemma reciprocityOk_true_iff (P : Policy A) (r : Request A) :
  reciprocityOk (P:=P) r = true ↔ ReciprocityOKP r := by
  simp [reciprocityOk, ReciprocityOKP]

@[simp] lemma temperanceOk_true_iff (P : Policy A) (r : Request A) :
  temperanceOk (P:=P) r = true ↔ TemperanceOKP r := by
  simp [temperanceOk, TemperanceOKP]

@[simp] lemma withinWindow_true_iff (r : Request A) :
  withinWindow r = true ↔ WithinWindowP r := by
  simp [withinWindow, WithinWindowP]

@[simp] lemma uniqueInWindow_true_iff (r : Request A) :
  uniqueInWindow r = true ↔ UniqueInWindowP r := by
  simp [uniqueInWindow, UniqueInWindowP]

@[simp] lemma fairnessOk_true_iff (r : Request A) :
  fairnessOk r = true ↔ FairnessOKP r := by
  simp [fairnessOk, FairnessOKP]

@[simp] lemma adversarialOk_true_iff (r : Request A) :
  adversarialOk r = true ↔ AdversarialOKP r := by
  simp [adversarialOk, AdversarialOKP]

@[simp] lemma truthOk_true_iff (P : Policy A) (r : Request A) :
  truthOk (P:=P) r = true ↔ TruthOKP (P:=P) r := by
  simp [truthOk, TruthOKP]

@[simp] lemma consentOk_true_iff (P : Policy A) (r : Request A) :
  consentOk (P:=P) r = true ↔ ConsentOKP (P:=P) r := by
  simp [consentOk, ConsentOKP]

@[simp] lemma harmOk_true_iff (P : Policy A) (r : Request A) :
  harmOk (P:=P) r = true ↔ HarmOKP (P:=P) r := by
  simp [harmOk, HarmOKP]

@[simp] lemma deonticOk_true_iff (P : Policy A) (r : Request A) :
  deonticOk (P:=P) r = true ↔ DeonticOKP (P:=P) r := by
  simp [deonticOk, DeonticOKP]

@[simp] lemma privacyOk_true_iff (P : Policy A) (r : Request A) :
  privacyOk (P:=P) r = true ↔ PrivacyOKP (P:=P) r := by
  simp [privacyOk, PrivacyOKP]

@[simp] lemma coiOk_true_iff (P : Policy A) (r : Request A) :
  coiOk (P:=P) r = true ↔ COIOKP (P:=P) r := by
  simp [coiOk, COIOKP]

@[simp] lemma robustOk_true_iff (P : Policy A) (r : Request A) :
  robustOk (P:=P) r = true ↔ RobustOKP (P:=P) r := by
  simp [robustOk, RobustOKP]

lemma admissible_true_iff (P : Policy A) (r : Request A) :
  admissible (P:=P) r = true ↔ Admissible P.period r.cq r.hasExperience := by
  classical
  by_cases h : Admissible P.period r.cq r.hasExperience
  · simp [admissible, h]
  · simp [admissible, h]

end Decision
end Ethics
end IndisputableMonolith

