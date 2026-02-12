import Mathlib
import IndisputableMonolith.LightLanguage.Meaning.Core

/-
# Motif Algebra and Expressiveness

Implements Step 3 of the semantic roadmap.  We model motifs as predicates on
canonical LNAL sequences, provide composition operators, and show that every
`Meaning` has a natural motif representation (expressiveness).  We also capture
a minimality property: any covering basis must include a motif whose carrier
contains the canonical sequence of each meaning it represents.
-/
namespace LightLanguage
namespace Meaning

open LightLanguage LNAL

/-- Canonical LNAL sequence associated with a meaning.  This is well-defined
because `Meaning` quotients signals by canonical-sequence equality. -/
noncomputable def canonicalSequenceOfMeaning :
    CanonicalMeaning → LNALSequence :=
  Quot.lift
    (fun signal => canonicalSequence defaultPipeline signal)
    (by
      intro s₁ s₂ h
      simpa [canonicalSequence, defaultPipeline, MeaningRel] using h)

@[simp] lemma canonicalSequenceOfMeaning_mk (signal : Signal) :
    canonicalSequenceOfMeaning ⟦signal⟧ₘ =
      canonicalSequence defaultPipeline signal := rfl

/-- Motifs are predicates on canonical LNAL sequences. -/
structure Motif where
  carrier : LNALSequence → Prop

namespace Motif

/-- Semantic satisfaction: a motif holds for a meaning iff its carrier accepts
the canonical sequence of that meaning. -/
def matches (m : Motif) (meaning : CanonicalMeaning) : Prop :=
  m.carrier (canonicalSequenceOfMeaning meaning)

/-- Atomic motif enforcing equality with a fixed canonical sequence. -/
def ofSequence (seq : LNALSequence) : Motif :=
  ⟨fun s => s = seq⟩

@[simp] lemma ofSequence_matches (seq : LNALSequence)
    (meaning : CanonicalMeaning) :
    (ofSequence seq).matches meaning ↔
      canonicalSequenceOfMeaning meaning = seq := by
  unfold matches ofSequence
  constructor
  · intro h
    simpa using h
  · intro h
    simpa [h]

/-- Sequential composition: concatenate canonical sequences witnessing each
motif. -/
def seq (m₁ m₂ : Motif) : Motif :=
  ⟨fun seq =>
      ∃ seq₁ seq₂, seq = seq₁ ++ seq₂ ∧ m₁.carrier seq₁ ∧ m₂.carrier seq₂⟩

/-- Repetition combinator (exactly `n` repetitions). -/
def rep : Motif → ℕ → Motif
  | m, 0 =>
      ofSequence []
  | m, Nat.succ n =>
      seq (rep m n) m

/-- Parallel/contextual composition, modelled as intersection of carriers. -/
def par (m₁ m₂ : Motif) : Motif :=
  ⟨fun seq => m₁.carrier seq ∧ m₂.carrier seq⟩

@[simp] lemma par_matches (m₁ m₂ : Motif) (meaning : CanonicalMeaning) :
    (par m₁ m₂).matches meaning ↔
      m₁.matches meaning ∧ m₂.matches meaning := by
  rfl

/-- Constructive assignment of a motif to any meaning: simply capture its
canonical sequence. -/
def ofMeaning (meaning : CanonicalMeaning) : Motif :=
  ofSequence (canonicalSequenceOfMeaning meaning)

@[simp] lemma ofMeaning_matches (meaning : CanonicalMeaning) :
    (ofMeaning meaning).matches meaning := by
  unfold ofMeaning matches
  simp

/-- Expressiveness: every meaning has a motif (obtained above) that matches it. -/
theorem expressiveness :
    ∀ meaning : CanonicalMeaning,
      (ofMeaning meaning).matches meaning := ofMeaning_matches

/-- Irredundancy/minimality: any basis of motifs that covers all meanings must
include (for each realised canonical sequence) a motif whose carrier contains
that sequence. -/
theorem basis_irredundant
    (basis : Set Motif)
    (covers : ∀ meaning, ∃ m ∈ basis, m.matches meaning)
    {seq : LNALSequence}
    (hexists : ∃ meaning, canonicalSequenceOfMeaning meaning = seq) :
    ∃ m ∈ basis, m.carrier seq := by
  classical
  rcases hexists with ⟨meaning, hseq⟩
  rcases covers meaning with ⟨m, hm_basis, hm_match⟩
  refine ⟨m, hm_basis, ?_⟩
  have : m.carrier (canonicalSequenceOfMeaning meaning) := hm_match
  simpa [hseq] using this

end Motif
end Meaning
end LightLanguage
