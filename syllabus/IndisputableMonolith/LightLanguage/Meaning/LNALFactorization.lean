import Mathlib
import IndisputableMonolith.LightLanguage.Meaning.MotifAlgebra

/-
# LNAL → Meaning Factorization

Implements Step 4 of the semantic development plan.  Every legality-preserving
LNAL program (already normalised) induces an endomorphism on canonical meanings
by acting on their canonical sequences.  Program equivalence is captured by
sequence-level congruence: two programs induce the same meaning morphism iff
they yield the same canonical sequence on every input.
-/
namespace LightLanguage
namespace Meaning

open LightLanguage LNAL

/-- Normalised LNAL programs (bodies are already in normal form). -/
structure Prog where
  body : LNALSequence
  canonical : NormalForm body
deriving Repr

namespace Prog

/-- Evaluate a program on a canonical sequence (concatenate then re-normalise). -/
def evalSequence (prog : Prog) (seq : LNALSequence) : LNALSequence :=
  reduce (seq ++ prog.body)

@[simp] lemma evalSequence_normal (prog : Prog) (seq : LNALSequence) :
    NormalForm (prog.evalSequence seq) := by
  unfold evalSequence NormalForm
  simp [evalSequence, NormalForm, LNAL.reduce_idem]

/-- Legality-preserving programs keep canonical sequences in normal form. -/
def LegalityPreserving (prog : Prog) : Prop :=
  ∀ seq, NormalForm seq → NormalForm (prog.evalSequence seq)

lemma legality (prog : Prog) : prog.LegalityPreserving := by
  intro seq _
  simpa using prog.evalSequence_normal seq

/-- Congruence of programs: they agree on all canonical sequences. -/
def Congruent (p₁ p₂ : Prog) : Prop :=
  ∀ seq, p₁.evalSequence seq = p₂.evalSequence seq

lemma congruent_refl (prog : Prog) : Congruent prog prog := by
  intro _; rfl

lemma congruent_symm {p₁ p₂ : Prog} :
    Congruent p₁ p₂ → Congruent p₂ p₁ := by
  intro h seq
  simpa [Congruent] using congrArg id (h seq)

lemma congruent_trans {p₁ p₂ p₃ : Prog} :
    Congruent p₁ p₂ → Congruent p₂ p₃ → Congruent p₁ p₃ := by
  intro h₁ h₂ seq
  exact (h₁ seq).trans (h₂ seq)

end Prog

/-- Canonical sequences extracted from meanings are always normal forms. -/
lemma canonicalSequenceOfMeaning_normal
    (meaning : CanonicalMeaning) :
    NormalForm (canonicalSequenceOfMeaning meaning) := by
  refine Quot.induction_on meaning ?_
  intro signal
  unfold canonicalSequenceOfMeaning canonicalSequence defaultPipeline
  simp [NormalForm, defaultAnalyze, defaultListen, defaultNormalize,
    LNAL.reduce_idem]

/-- Action of a normalised LNAL program on meanings. -/
def act (prog : Prog) (meaning : CanonicalMeaning) : CanonicalMeaning :=
  ⟦ prog.evalSequence (canonicalSequenceOfMeaning meaning) ⟧ₘ

@[simp] lemma canonicalSequence_act (prog : Prog) (meaning : CanonicalMeaning) :
    canonicalSequenceOfMeaning (prog.act meaning) =
      prog.evalSequence (canonicalSequenceOfMeaning meaning) := by
  unfold act canonicalSequenceOfMeaning
  simp [Prog.evalSequence, canonicalSequence, defaultPipeline,
    defaultAnalyze, defaultListen, defaultNormalize, LNAL.reduce_idem]

/-- Program actions are meaning endomorphisms (normal-form outputs). -/
lemma act_preserves_normal (prog : Prog) (meaning : CanonicalMeaning) :
    NormalForm (canonicalSequenceOfMeaning (prog.act meaning)) := by
  simpa [canonicalSequence_act] using prog.evalSequence_normal _

/-- Congruent programs induce the same meaning morphism. -/
theorem act_congr {p₁ p₂ : Prog}
    (h : Prog.Congruent p₁ p₂) :
    p₁.act = p₂.act := by
  funext meaning
  unfold Prog.act
  have hseq := h (canonicalSequenceOfMeaning meaning)
  apply Meaning.interpret_eq_of_sequence_eq defaultPipeline
  simpa [canonicalSequence, defaultPipeline, defaultAnalyze, defaultListen,
    defaultNormalize, Prog.evalSequence] using hseq

/-- Identity program (empty body) acts trivially on meanings. -/
def idProg : Prog :=
  { body := []
    canonical := by
      unfold NormalForm
      simp }

@[simp] lemma act_id (meaning : CanonicalMeaning) :
    idProg.act meaning = meaning := by
  refine Quot.induction_on meaning ?_
  intro seq
  unfold idProg act Prog.evalSequence
  simp [canonicalSequenceOfMeaning_mk, canonicalSequence, defaultPipeline,
    defaultAnalyze, defaultListen, defaultNormalize, List.nil_append,
    LNAL.reduce_idem]

/-- Composition of program bodies corresponds to composition of actions. -/
def compose (p₁ p₂ : Prog) : Prog :=
  { body := reduce (p₁.body ++ p₂.body)
    canonical := by
      unfold NormalForm
      simp [LNAL.reduce_idem] }

lemma act_compose (p₁ p₂ : Prog) (meaning : CanonicalMeaning) :
    (compose p₁ p₂).act meaning =
      p₂.act (p₁.act meaning) := by
  unfold compose act Prog.evalSequence
  simp [List.append_assoc, canonicalSequence_act, LNAL.reduce_idem]

/-- Example: if program bodies share the same canonical (reduced) form, they are
congruent and thus define identical meaning actions. -/
lemma congruent_of_body_reduce_eq {p₁ p₂ : Prog}
    (h : reduce p₁.body = reduce p₂.body) :
    Prog.Congruent p₁ p₂ := by
  intro seq
  simp [Prog.evalSequence, List.append_assoc, h]

end Meaning
end LightLanguage
