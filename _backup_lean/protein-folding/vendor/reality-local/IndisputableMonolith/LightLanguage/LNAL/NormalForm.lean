import Mathlib
import IndisputableMonolith.LightLanguage.LNAL.Operators

/-!
## LNAL Normal Forms

We implement a lightweight reduction system that removes bookkeeping
instructions (`listen`, `balance`, `fold`, and illegal `braid`s) while
retaining the structural ones (`lock`s and legal `braid`s).  All proofs
use elementary list combinatorics.
-/
namespace LightLanguage.LNAL

open StructuredSet

attribute [simp] List.length_append

/-- Primitive LNAL instructions. -/
inductive LNALOp
  | listen
  | lock (indices : List ℕ)
  | balance (indices : List ℕ)
  | fold (indices : List ℕ)
  | braid (triad : Fin 3 → ℕ)
  deriving DecidableEq, Repr

/-- Convenience alias for instruction sequences. -/
abbrev LNALSequence := List LNALOp

/-- Local normalisation of a single instruction. -/
@[simp] def normalizeOp : LNALOp → Option LNALOp
  | LNALOp.listen => none
  | LNALOp.lock idx => some (LNALOp.lock idx)
  | LNALOp.balance _ => none
  | LNALOp.fold _ => none
  | LNALOp.braid triad =>
      if LegalTriad (triad 0) (triad 1) (triad 2) then
        some (LNALOp.braid triad)
      else
        none

@[simp] lemma normalizeOp_braid_legal {triad : Fin 3 → ℕ}
    (h : LegalTriad (triad 0) (triad 1) (triad 2)) :
    normalizeOp (LNALOp.braid triad) = some (LNALOp.braid triad) := by
  simp [normalizeOp, h]

@[simp] lemma normalizeOp_braid_illegal {triad : Fin 3 → ℕ}
    (h : ¬ LegalTriad (triad 0) (triad 1) (triad 2)) :
    normalizeOp (LNALOp.braid triad) = none := by
  simp [normalizeOp, h]

/-- Canonical reduction obtained by filtering instructions. -/
@[simp] def reduce (seq : LNALSequence) : LNALSequence :=
  seq.filterMap normalizeOp

@[simp] lemma reduce_nil : reduce ([] : LNALSequence) = [] := rfl
@[simp] lemma reduce_cons_listen (seq : LNALSequence) :
    reduce (LNALOp.listen :: seq) = reduce seq := by
  simp [reduce]
@[simp] lemma reduce_cons_balance (idx : List ℕ) (seq : LNALSequence) :
    reduce (LNALOp.balance idx :: seq) = reduce seq := by
  simp [reduce]
@[simp] lemma reduce_cons_fold (idx : List ℕ) (seq : LNALSequence) :
    reduce (LNALOp.fold idx :: seq) = reduce seq := by
  simp [reduce]
@[simp] lemma reduce_cons_lock (idx : List ℕ) (seq : LNALSequence) :
    reduce (LNALOp.lock idx :: seq) = LNALOp.lock idx :: reduce seq := by
  simp [reduce]
@[simp] lemma reduce_cons_legal_braid {triad : Fin 3 → ℕ}
    (h : LegalTriad (triad 0) (triad 1) (triad 2)) (seq : LNALSequence) :
    reduce (LNALOp.braid triad :: seq) = LNALOp.braid triad :: reduce seq := by
  simp [reduce, normalizeOp, h]
lemma reduce_cons_illegal_braid {triad : Fin 3 → ℕ}
    (h : ¬ LegalTriad (triad 0) (triad 1) (triad 2)) (seq : LNALSequence) :
    reduce (LNALOp.braid triad :: seq) = reduce seq := by
  simp [reduce, normalizeOp, h]

/-- Local one-step reduction relation. -/
inductive LocalReduction : LNALSequence → LNALSequence → Prop
  | drop_listen (pre suf : LNALSequence) :
      LocalReduction (pre ++ LNALOp.listen :: suf) (pre ++ suf)
  | drop_balance (pre suf : LNALSequence) (idx : List ℕ) :
      LocalReduction (pre ++ LNALOp.balance idx :: suf) (pre ++ suf)
  | drop_illegal_braid (pre suf : LNALSequence) (triad : Fin 3 → ℕ)
      (h : ¬ LegalTriad (triad 0) (triad 1) (triad 2)) :
      LocalReduction (pre ++ LNALOp.braid triad :: suf) (pre ++ suf)
  | drop_fold (pre suf : LNALSequence) (idx : List ℕ) :
      LocalReduction (pre ++ LNALOp.fold idx :: suf) (pre ++ suf)

namespace LocalReduction

@[simp] lemma length_lt {seq seq' : LNALSequence} :
    LocalReduction seq seq' → seq'.length < seq.length := by
  intro h
  classical
  cases h with
  | drop_listen pre suf =>
      simp [Nat.add_comm, Nat.add_left_comm, Nat.succ_eq_add_one]
  | drop_balance pre suf idx =>
      simp [Nat.add_comm, Nat.add_left_comm, Nat.succ_eq_add_one]
  | drop_illegal_braid pre suf triad h =>
      simp [Nat.add_comm, Nat.add_left_comm, Nat.succ_eq_add_one]
  | drop_fold pre suf idx =>
      simp [Nat.add_comm, Nat.add_left_comm, Nat.succ_eq_add_one]

lemma preserves_reduce {seq seq' : LNALSequence}
    (h : LocalReduction seq seq') : reduce seq = reduce seq' := by
  classical
  cases h with
  | drop_listen pre suf =>
      simp [reduce, List.filterMap_append]
  | drop_balance pre suf idx =>
      simp [reduce, List.filterMap_append]
  | drop_illegal_braid pre suf triad h =>
      simp [reduce, List.filterMap_append, normalizeOp, h]
  | drop_fold pre suf idx =>
      simp [reduce, List.filterMap_append]

lemma context {pre post a b : LNALSequence}
    (h : LocalReduction a b) :
    LocalReduction (pre ++ a ++ post) (pre ++ b ++ post) := by
  classical
  cases h with
  | drop_listen pre₀ suf =>
      simpa [List.append_assoc] using
        LocalReduction.drop_listen (pre := pre ++ pre₀) (suf := suf ++ post)
  | drop_balance pre₀ suf idx =>
      simpa [List.append_assoc] using
        LocalReduction.drop_balance (pre := pre ++ pre₀) (suf := suf ++ post) (idx := idx)
  | drop_illegal_braid pre₀ suf triad h =>
      simpa [List.append_assoc] using
        LocalReduction.drop_illegal_braid
          (pre := pre ++ pre₀) (suf := suf ++ post) (triad := triad) h
  | drop_fold pre₀ suf idx =>
      simpa [List.append_assoc] using
        LocalReduction.drop_fold (pre := pre ++ pre₀) (suf := suf ++ post) (idx := idx)

lemma cons_left {op : LNALOp} {seq seq' : LNALSequence} :
    LocalReduction seq seq' →
    LocalReduction (op :: seq) (op :: seq') := by
  intro h
  classical
  simpa using context (pre := [op]) (post := ([] : LNALSequence)) h

end LocalReduction

lemma reflTransGen_cons_left {op : LNALOp} :
    ∀ {seq seq' : LNALSequence},
      Relation.ReflTransGen LocalReduction seq seq' →
      Relation.ReflTransGen LocalReduction (op :: seq) (op :: seq')
  | _, _, Relation.ReflTransGen.refl _ => Relation.ReflTransGen.refl _
  | _, _, Relation.ReflTransGen.tail h rest =>
      Relation.ReflTransGen.tail (LocalReduction.cons_left h)
        (reflTransGen_cons_left rest)

/-- Placeholder execution: every sequence acts trivially. -/
def execute (_seq : LNALSequence) (initial : LedgerState) : LedgerState := initial

/-- A normal form is a fixed point of `reduce`. -/
def NormalForm (seq : LNALSequence) : Prop := seq = reduce seq

lemma reduce_length_le (seq : LNALSequence) :
    (reduce seq).length ≤ seq.length := by
  classical
  induction seq with
  | nil => simp
  | cons op rest ih =>
      cases op with
      | listen =>
          simpa using ih
      | lock idx =>
          simpa [reduce_cons_lock] using Nat.succ_le_succ ih
      | balance idx =>
          simpa using ih
      | fold idx =>
          simpa using ih
      | braid triad =>
          by_cases h : LegalTriad (triad 0) (triad 1) (triad 2)
          · simpa [reduce_cons_legal_braid, h] using Nat.succ_le_succ ih
          · simpa [reduce_cons_illegal_braid, h] using ih

lemma reduction_to_reduce :
    ∀ seq : LNALSequence, Relation.ReflTransGen LocalReduction seq (reduce seq)
  | [] => Relation.ReflTransGen.refl _
  | LNALOp.listen :: rest =>
      Relation.ReflTransGen.tail
        (LocalReduction.drop_listen [] rest)
        (reduction_to_reduce rest)
  | LNALOp.lock idx :: rest =>
      by
        have h := reduction_to_reduce rest
        have := Relation.ReflTransGen.congr_left (LocalReduction.cons_left (seq := rest) (seq' := reduce rest)) h
        (???)
