import Mathlib
import IndisputableMonolith.LightLanguage.LNAL.NormalForm

/-
# Meaning Core (ULL Denotational Semantics)

This module provides the logical scaffolding for Step 1 of the ULL semantic
plan.  We formalise the LISTEN → ANALYZE → NORMALIZE pipeline at the type level,
turn signals into equivalence classes (Meanings), and prove basic invariance
facts that subsequent steps (universality, motif algebra, factorisation, ethics
bridge) will build on.
-/
namespace LightLanguage
namespace Meaning

open LightLanguage.LNAL

/-- In the logic-only development we treat signals as symbolic LNAL sequences.
Any future, physically grounded signal model can be substituted by giving a new
`Pipeline`. -/
abbrev Signal := LNALSequence

/-- Canonical windows coincide with symbolic sequences in the logic scaffold.
This keeps the LISTEN → ANALYZE → NORMALIZE pipeline explicit while avoiding
unnecessary sensor bookkeeping. -/
abbrev CanonicalWindows := LNALSequence

/-- A pipeline packages the three logical stages LISTEN → ANALYZE → NORMALIZE.
`normalize` is required to be idempotent; concrete instances can use `reduce`
from `LNAL.NormalForm` or any other normal-form procedure. -/
structure Pipeline where
  listen : Signal → CanonicalWindows
  analyze : CanonicalWindows → LNALSequence
  normalize : LNALSequence → LNALSequence
  normalize_idem : ∀ seq, normalize (normalize seq) = normalize seq

/-- Canonical LNAL sequence associated with a signal under a pipeline. -/
def canonicalSequence (P : Pipeline) (signal : Signal) : LNALSequence :=
  P.normalize (P.analyze (P.listen signal))

/-- Equivalence relation induced by the canonical sequence.
This is the core definition of semantic equivalence in ULL: two signals mean
the same thing if and only if they reduce to the same canonical normal form. -/
def MeaningRel (P : Pipeline) (s₁ s₂ : Signal) : Prop :=
  canonicalSequence P s₁ = canonicalSequence P s₂

namespace LNAL

@[simp] lemma normalizeOp_bind_self (op : LNALOp) :
    Option.bind (normalizeOp op) normalizeOp = normalizeOp op := by
  cases op <;> simp [normalizeOp]
  · -- braid case
    by_cases h : LegalTriad (_ 0) (_ 1) (_ 2) <;> simp [normalizeOp, h]

lemma List.filterMap_eq_self_of_forall {α : Type _}
    (f : α → Option α) :
    ∀ {l : List α}, (∀ a ∈ l, f a = some a) → l.filterMap f = l
  | [], _ => rfl
  | a :: l, h =>
      have h' := List.forall_mem_cons.mp h
      simp [List.filterMap, h'.1, filterMap_eq_self_of_forall f (l := l) h'.2]

lemma normalizeOp_of_mem_reduce {op : LNALOp} {seq : LNALSequence}
    (h : op ∈ reduce seq) : normalizeOp op = some op := by
  classical
  unfold reduce at h
  obtain ⟨op', hop', hnorm⟩ := List.mem_filterMap.mp h
  cases op' with
  | listen => simp [normalizeOp] at hnorm
  | lock idx =>
      simpa [normalizeOp] using hnorm
  | balance _ => simp [normalizeOp] at hnorm
  | fold _ => simp [normalizeOp] at hnorm
  | braid triad =>
      by_cases htri : LegalTriad (triad 0) (triad 1) (triad 2)
      · have : op = LNALOp.braid triad := by
          simpa [normalizeOp, htri] using hnorm
        simpa [this, normalizeOp, htri]
      · simp [normalizeOp, htri] at hnorm

/-- `reduce` is idempotent, so it can serve as a canonical normaliser. -/
@[simp] lemma reduce_idem (seq : LNALSequence) :
    reduce (reduce seq) = reduce seq := by
  classical
  have hfix : ∀ op ∈ reduce seq, normalizeOp op = some op :=
    by intro op hop; exact normalizeOp_of_mem_reduce hop
  simpa [reduce] using
    List.filterMap_eq_self_of_forall (normalizeOp) (l := reduce seq) hfix

end LNAL

/-- Setoid identifying signals with the same canonical sequence. -/
def meaningSetoid (P : Pipeline) : Setoid Signal where
  R := MeaningRel P
  iseqv :=
    { refl := by intro s; rfl
      symm := by
        intro a b h
        simpa [MeaningRel] using h.symm
      trans := by
        intro a b c h₁ h₂
        exact h₁.trans h₂ }

/-- Meaning is the quotient of signals by canonical-sequence equality.
This type represents the "Periodic Table of Meaning" abstractly: elements of this
type are the unique semantic values that signals map to.

Universality Stub:
This definition is the target of the `PerfectLanguageCert` theorem (Step 2).
We will prove that this `Meaning` type, when instantiated with the RS-forced
pipeline, is the initial object in the category of zero-parameter semantic encoders.
-/
abbrev Meaning (P : Pipeline) := Quot (meaningSetoid P)

namespace Meaning

/-- Interpretation map `⟦·⟧ : Signal → Meaning`. -/
def interpret (P : Pipeline) (signal : Signal) : Meaning P :=
  Quot.mk _ signal

@[simp] lemma interpret_eq_iff (P : Pipeline) (s₁ s₂ : Signal) :
    interpret P s₁ = interpret P s₂ ↔
      canonicalSequence P s₁ = canonicalSequence P s₂ := by
  constructor
  · intro h
    have := Quot.eq.mp h
    simpa [MeaningRel] using this
  · intro h
    exact Quot.eq.mpr (by simpa [MeaningRel])

lemma interpret_eq_of_sequence_eq (P : Pipeline) {s₁ s₂ : Signal}
    (h : canonicalSequence P s₁ = canonicalSequence P s₂) :
    interpret P s₁ = interpret P s₂ := by
  simpa [interpret_eq_iff] using h

/-- Sensor invariance: if a transformation preserves canonical sequences, it
preserves meaning. -/
lemma interpret_sensor_invariant (P : Pipeline)
    (sensor : Signal → Signal)
    (h : ∀ signal, canonicalSequence P (sensor signal) =
        canonicalSequence P signal) :
    ∀ signal, interpret P (sensor signal) = interpret P signal := by
  intro signal
  exact interpret_eq_of_sequence_eq P (h signal)

/-- Carrier invariance: if two acquisition chains map raw data to the same
canonical sequence, they agree on meaning. -/
lemma interpret_carrier_invariant (P : Pipeline)
    (carrier₁ carrier₂ : Signal → Signal)
    (h : ∀ signal,
        canonicalSequence P (carrier₁ signal) =
        canonicalSequence P (carrier₂ signal)) :
    ∀ signal,
        interpret P (carrier₁ signal) =
        interpret P (carrier₂ signal) := by
  intro signal
  exact interpret_eq_of_sequence_eq P (h signal)

end Meaning

/-- LISTEN stage for the symbolic scaffold: expose the latent sequence. -/
def defaultListen : Signal → CanonicalWindows :=
  id

/-- ANALYZE stage for the symbolic scaffold: identity on canonical windows. -/
def defaultAnalyze : CanonicalWindows → LNALSequence :=
  id

/-- Canonical NORMALIZE stage built from LNAL `reduce`. -/
def defaultNormalize : LNALSequence → LNALSequence :=
  reduce

lemma defaultNormalize_idem :
    ∀ seq, defaultNormalize (defaultNormalize seq) = defaultNormalize seq := by
  intro seq
  simpa using LNAL.reduce_idem seq

/-- Canonical pipeline combining the three symbolic stages. -/
def defaultPipeline : Pipeline :=
  { listen := defaultListen
    analyze := defaultAnalyze
    normalize := defaultNormalize
    normalize_idem := defaultNormalize_idem }

/-- Default meaning type used throughout the development. -/
abbrev CanonicalMeaning := Meaning defaultPipeline

/-- Default interpretation map (notation `⟦·⟧ₘ`). -/
notation "⟦" signal "⟧ₘ" => Meaning.interpret defaultPipeline signal

/-- Helper: canonical sequences of symbolic signals are just `reduce`. -/
@[simp] lemma canonicalSequence_default (signal : Signal) :
    canonicalSequence defaultPipeline signal = reduce signal := rfl

end Meaning
end LightLanguage
