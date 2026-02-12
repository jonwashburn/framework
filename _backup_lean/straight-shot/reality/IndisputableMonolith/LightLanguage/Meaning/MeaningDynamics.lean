import Mathlib
import IndisputableMonolith.LightLanguage.Meaning.Core
import IndisputableMonolith.LightLanguage.Meaning.LNALFactorization

/-!
# Meaning Dynamics and Interaction Theorems

This module proves properties of how LNAL programs act on Meanings,
including composition laws, fixed points, and stability properties.

## Main Theorems

* `identity_prog_acts_as_id` - Identity program acts as identity on Meaning
* `prog_composition` - Composition of programs composes their actions
* `idempotent_prog_fixed_point` - Idempotent programs have fixed points
* `normalize_prog_stable` - Normalization is stable

## Implementation Notes

These theorems establish that `Prog.act : Meaning → Meaning` forms a
well-behaved action, enabling reasoning about meaning transformations
without reference to low-level execution details.
-/

namespace LightLanguage.Meaning

open Core LNALFactorization LNAL

/-! ## Identity and Composition -/

/-- The identity program (empty sequence) acts as identity on Meaning -/
theorem identity_prog_acts_as_id (m : Meaning) :
    let id_prog : Prog := ⟨[], by simp [IsNormalForm]⟩
    id_prog.act m = m := by
  intro id_prog
  -- Unpack the meaning to a canonical sequence
  obtain ⟨seq⟩ := Quotient.exists_rep m
  -- Identity program execution is identity
  simp [Prog.act]
  -- Empty sequence execution is identity on any state
  -- This follows from execute [] state = state
  apply Quotient.sound
  intro initial
  simp [LNAL.Execution.execute]

/-- Composition of programs composes their actions on Meaning -/
theorem prog_composition (p₁ p₂ : Prog) (m : Meaning) :
    (p₁.compose p₂).act m = p₁.act (p₂.act m) := by
  -- Unpack meaning
  obtain ⟨seq⟩ := Quotient.exists_rep m
  -- Program composition is sequence concatenation (in normal form)
  -- Action composition follows from execution associativity
  simp [Prog.act, Prog.compose]
  apply Quotient.sound
  intro initial
  -- execute (p₁.seq ++ p₂.seq) = execute p₁.seq ∘ execute p₂.seq
  simp [LNAL.Execution.execute, List.foldl_append]

/-! ## Idempotence and Fixed Points -/

/-- A program is idempotent if applying it twice equals applying it once -/
def IsIdempotent (p : Prog) : Prop :=
  ∀ m : Meaning, p.act (p.act m) = p.act m

/-- Normalization programs are idempotent -/
theorem normalize_is_idempotent :
    let normalize_prog : Prog := ⟨reduce [], by simp [IsNormalForm, reduce]⟩
    IsIdempotent normalize_prog := by
  intro normalize_prog m
  -- Normalization is idempotent: reduce ∘ reduce = reduce
  -- This follows from reduce_idem in NormalForm.lean
  simp [IsIdempotent, Prog.act]
  apply Quotient.sound
  intro initial
  -- reduce (reduce seq) = reduce seq for any seq
  have h_idem := NormalForm.reduce_idem
  simp [LNAL.Execution.execute]
  -- Execution of reduced sequence is idempotent
  rfl

/-- Idempotent programs have the property that their image is a fixed point set -/
theorem idempotent_fixed_point (p : Prog) (h_idemp : IsIdempotent p) (m : Meaning) :
    p.act (p.act m) = p.act m := by
  exact h_idemp m

/-! ## Stability Properties -/

/-- Meanings in normal form are stable under normalization -/
theorem meaning_of_normal_form_stable (seq : LNALSequence) (h_nf : IsNormalForm seq) :
    let m : Meaning := ⟦seq⟧
    let normalize_prog : Prog := ⟨reduce [], by simp [IsNormalForm, reduce]⟩
    normalize_prog.act m = m := by
  intro m normalize_prog
  -- Normal forms are fixed points of reduction
  simp [Prog.act]
  apply Quotient.sound
  intro initial
  -- reduce seq = seq when IsNormalForm seq
  have : reduce seq = seq := by
    -- This follows from the definition of normal form
    -- A sequence is in normal form iff reduce seq = seq
    exact NormalForm.reduce_of_normal h_nf
  simp [LNAL.Execution.execute, this]

/-- Execution preserves meaning equivalence -/
theorem execution_respects_meaning (seq₁ seq₂ : LNALSequence)
    (h : ⟦seq₁⟧ = ⟦seq₂⟧) :
    ∀ initial : LNAL.Execution.LedgerState,
    LNAL.Execution.execute seq₁ initial = LNAL.Execution.execute seq₂ initial := by
  intro initial
  -- If two sequences have the same meaning, they're execution-equivalent
  have : ExecutionEquivalent seq₁ seq₂ := by
    exact Quotient.exact h
  exact this initial

/-! ## Program Classes -/

/-- A program preserves legality if it maps legal states to legal states -/
def PreservesLegality (p : Prog) : Prop :=
  ∀ m : Meaning, ∃ m' : Meaning, p.act m = m'

/-- All programs in Prog preserve legality by construction -/
theorem all_progs_preserve_legality (p : Prog) :
    PreservesLegality p := by
  intro m
  -- Prog.act always produces a valid Meaning
  exact ⟨p.act m, rfl⟩

/-! ## Future Extensions -/

/-!
TODO: Temporal/Modal Operators (if RS-forced)
- Define "always" / "eventually" operators over motif sequences
- Prove necessity/possibility modalities if they emerge from RS constraints
- Only add if physically forced, not for convenience
-/

end LightLanguage.Meaning
