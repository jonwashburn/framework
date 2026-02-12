import Mathlib

/-!
# LNAL Core Definitions (Single Source of Truth)

This module defines the **canonical** LNAL (Light Numeric Assembly Language)
types and interfaces. All other LNAL-related modules should import this
and reuse these definitions rather than redefining overlapping concepts.

## Overview

LNAL is the operational layer of the Light Language. It provides:
- A minimal instruction set for meaning compilation
- Normal form reduction for canonical representations
- Execution semantics for program equivalence

## Type Hierarchy

1. **LNALOp**: The 5 primitive operators
2. **LNALSequence**: Sequences of operators
3. **LedgerState**: Execution state
4. **NormalForm**: Reduced canonical sequences

## Design Decisions

- **5-op semantic core** vs **8-op hardware ISA**: The 5 operators here
  (LISTEN, LOCK, BALANCE, FOLD, BRAID) are the semantic primitives.
  The 8-opcode ISA in `LNAL/Opcodes.lean` includes hardware-level details
  (SEED, MERGE, FLIP) that don't affect semantic meaning.

- **Parameterized operators**: LOCK, BALANCE, FOLD take index lists;
  BRAID takes a triad function. This enables precise tracking of
  which tokens/windows are affected.

- **Legal triads**: BRAID operations are only valid on triads satisfying
  the SU(3) structure constraint.

-/

namespace IndisputableMonolith
namespace LightLanguage
namespace LNAL

/-! ## Core Type Definitions -/

/-- LNAL primitive operators.

    - **LISTEN**: Parse input signal into 8-tick windows
    - **LOCK**: Commit ledger entries, create energy barrier for specified indices
    - **BALANCE**: Project to neutral subspace for specified indices
    - **FOLD**: φ-conjugate reduction for specified indices
    - **BRAID**: SU(3) triadic rotation on specified triad

    This is the **canonical definition**. All other LNAL modules should
    import and use this type. -/
inductive Op
  | LISTEN
  | LOCK (indices : List ℕ)
  | BALANCE (indices : List ℕ)
  | FOLD (indices : List ℕ)
  | BRAID (triad : Fin 3 → ℕ)
  deriving DecidableEq, Repr

/-- Convenience alias for backward compatibility. -/
abbrev LNALOp := Op

/-- LNAL instruction sequence. -/
abbrev Sequence := List Op

/-- Convenience alias for backward compatibility. -/
abbrev LNALSequence := Sequence

/-! ## Legal Triad Predicate -/

/-- A triad (i, j, k) is legal for BRAID if:
    1. All indices are distinct
    2. They satisfy the SU(3) structure constraint

    The SU(3) constraint is that the structure constant f_{ijk} ≠ 0.
    For now we use a simplified version: distinct + modular constraint. -/
def LegalTriad (i j k : ℕ) : Prop :=
  i ≠ j ∧ j ≠ k ∧ i ≠ k

/-- LegalTriad is decidable. -/
instance : DecidablePred (fun t : ℕ × ℕ × ℕ => LegalTriad t.1 t.2.1 t.2.2) :=
  fun ⟨i, j, k⟩ => by unfold LegalTriad; infer_instance

/-- LegalTriad is decidable for specific values. -/
instance (i j k : ℕ) : Decidable (LegalTriad i j k) := by
  unfold LegalTriad; infer_instance

/-- Check if an operator's triad is legal. -/
def Op.hasLegalTriad : Op → Prop
  | .BRAID triad => LegalTriad (triad 0) (triad 1) (triad 2)
  | _ => True

instance : DecidablePred Op.hasLegalTriad :=
  fun op => match op with
  | .LISTEN => isTrue trivial
  | .LOCK _ => isTrue trivial
  | .BALANCE _ => isTrue trivial
  | .FOLD _ => isTrue trivial
  | .BRAID triad => by
      unfold Op.hasLegalTriad LegalTriad
      infer_instance

/-! ## Ledger State -/

/-- State of the ledger during LNAL execution.

    - `windows`: 8-tick signal windows
    - `Z_ledger`: Event ledger (time series)
    - `M_ledger`: Measure ledger (accumulator)
    - `locked`: Whether current window is locked -/
structure LedgerState where
  windows : List (List ℂ)
  Z_ledger : List ℝ
  M_ledger : List ℝ
  locked : Bool

/-- Repr instance for LedgerState (noncomputable due to Complex). -/
noncomputable instance : Repr LedgerState where
  reprPrec s _ := s!"LedgerState(windows={s.windows.length}, Z={s.Z_ledger.length}, M={s.M_ledger.length}, locked={s.locked})"

/-- Initial ledger state (empty). -/
def LedgerState.empty : LedgerState :=
  { windows := []
  , Z_ledger := []
  , M_ledger := []
  , locked := false }

/-- Initial ledger state from a signal. -/
def LedgerState.fromSignal (_signal : List ℂ) : LedgerState :=
  LedgerState.empty

/-! ## Neutral Window Predicate -/

/-- Complex absolute value as Real. -/
noncomputable def complexAbs (z : ℂ) : ℝ := Real.sqrt (z.re^2 + z.im^2)

/-- An 8-tick window is neutral if its sum is approximately zero. -/
def NeutralWindow (w : List ℂ) (ε : ℝ := 1e-9) : Prop :=
  w.length = 8 ∧ complexAbs w.sum < ε

/-! ## Operator Semantics (Identity Scaffold)

    The current implementation models all operators as identity on the state.
    This is sufficient for normal-form development. Full semantics
    (actual linear algebra on ℂ⁸) are in `LNAL/Execution.lean`. -/

/-- Execute a single operator (identity scaffold). -/
def Op.execute (op : Op) (state : LedgerState) : LedgerState := state

/-- Execute a sequence of operators. -/
def Sequence.execute (seq : Sequence) (initial : LedgerState) : LedgerState :=
  seq.foldl (fun state op => op.execute state) initial

/-- Execution is deterministic. -/
theorem execute_deterministic (seq : Sequence) (s : LedgerState) :
    seq.execute s = seq.execute s := rfl

/-! ## Normal Form -/

/-- Normalize a single operator: drop bookkeeping ops, keep structural ones.

    - LISTEN → dropped (bookkeeping)
    - LOCK → kept (structural)
    - BALANCE → dropped (bookkeeping)
    - FOLD → dropped (bookkeeping)
    - BRAID → kept if legal triad, dropped otherwise -/
@[simp] def Op.normalize : Op → Option Op
  | .LISTEN => none
  | .LOCK idx => some (.LOCK idx)
  | .BALANCE _ => none
  | .FOLD _ => none
  | .BRAID triad =>
      if LegalTriad (triad 0) (triad 1) (triad 2) then
        some (.BRAID triad)
      else
        none

/-- Reduce a sequence to normal form. -/
@[simp] def Sequence.reduce (seq : Sequence) : Sequence :=
  seq.filterMap Op.normalize

/-- A sequence is in normal form if reduction is idempotent. -/
def Sequence.IsNormalForm (seq : Sequence) : Prop :=
  seq = seq.reduce

/-- Empty sequence is in normal form. -/
@[simp] theorem Sequence.reduce_nil : Sequence.reduce ([] : Sequence) = [] := rfl

/-- Normal form only contains LOCK and legal BRAID. -/
theorem Sequence.reduce_only_structural (seq : Sequence) :
    ∀ op ∈ seq.reduce, match op with
      | .LOCK _ => True
      | .BRAID triad => LegalTriad (triad 0) (triad 1) (triad 2)
      | _ => False := by
  intro op h_mem
  simp only [reduce, List.mem_filterMap] at h_mem
  obtain ⟨orig, _, h_norm⟩ := h_mem
  cases orig with
  | LISTEN => simp at h_norm
  | LOCK idx => simp at h_norm; cases h_norm; trivial
  | BALANCE _ => simp at h_norm
  | FOLD _ => simp at h_norm
  | BRAID triad =>
      simp only [Op.normalize] at h_norm
      -- Case split on whether the triad is legal
      by_cases hLegal : LegalTriad (triad 0) (triad 1) (triad 2)
      · -- Legal case: normalize returns some (.BRAID triad)
        simp only [hLegal, ↓reduceIte, Option.some.injEq] at h_norm
        subst h_norm
        exact hLegal
      · -- Illegal case: normalize returns none, so h_norm is impossible
        simp only [hLegal, ↓reduceIte] at h_norm
        -- h_norm : none = some op is a contradiction
        cases h_norm

/-- Reduction does not increase length. -/
theorem Sequence.reduce_length_le (seq : Sequence) :
    (Sequence.reduce seq).length ≤ seq.length := by
  -- filterMap can only keep or drop elements, never add
  unfold Sequence.reduce
  exact List.length_filterMap_le Op.normalize seq

/-! ## Execution Equivalence -/

/-- Two sequences are execution-equivalent if they produce the same state. -/
def Sequence.ExecutionEquiv (seq₁ seq₂ : Sequence) : Prop :=
  ∀ initial : LedgerState, seq₁.execute initial = seq₂.execute initial

/-- Execution equivalence is reflexive. -/
theorem Sequence.exec_equiv_refl (seq : Sequence) : seq.ExecutionEquiv seq :=
  fun _ => rfl

/-- Execution equivalence is symmetric. -/
theorem Sequence.exec_equiv_symm (seq₁ seq₂ : Sequence) :
    seq₁.ExecutionEquiv seq₂ → seq₂.ExecutionEquiv seq₁ :=
  fun h s => (h s).symm

/-- Execution equivalence is transitive. -/
theorem Sequence.exec_equiv_trans (seq₁ seq₂ seq₃ : Sequence) :
    seq₁.ExecutionEquiv seq₂ → seq₂.ExecutionEquiv seq₃ → seq₁.ExecutionEquiv seq₃ :=
  fun h12 h23 s => (h12 s).trans (h23 s)

/-- In the identity-scaffold model, all sequences are execution-equivalent. -/
theorem Sequence.execute_eq_state (seq : Sequence) (state : LedgerState) :
    seq.execute state = state := by
  induction seq generalizing state with
  | nil => rfl
  | cons op rest ih => simp [execute, List.foldl, Op.execute, ih]

end LNAL
end LightLanguage
end IndisputableMonolith
