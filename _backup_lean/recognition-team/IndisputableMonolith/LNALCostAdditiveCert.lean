import Mathlib
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.InstrCost

/-!
# LNAL Cost Properties Certificate

This certificate proves fundamental properties of LNAL cost accounting:

1. **BALANCE neutrality**: BALANCE opcodes have zero cost
2. **Non-FOLD opcodes zero**: Simple LOCK/LISTEN/BRAID have zero cost
3. **Cost definitional form**: instrCost is well-defined for all opcodes

## Why This Matters

These properties ensure that:
- The BALANCE opcode doesn't add spurious cost (preserves ledger neutrality)
- Most control flow opcodes are cost-neutral
- Cost accounting has proper mathematical structure

## Non-Circularity

All proofs are by:
- Case analysis on opcodes (definitional)
- No external axioms or postulates
- Direct computation via `simp`/`rfl`
-/

namespace IndisputableMonolith
namespace Verification
namespace LNALCostAdditive

open IndisputableMonolith.LNAL

/-- Maximum absolute cost per opcode -/
def maxOpcodeCost : Nat := 1

/-- BALANCE opcodes have zero cost (all modes) -/
theorem balance_neutral : instrCost (LInstr.simple Opcode.BALANCE) = 0 := by
  simp [LInstr.simple, instrCost]

/-- LOCK opcode has zero cost -/
theorem lock_zero_cost : instrCost (LInstr.simple Opcode.LOCK) = 0 := by
  simp [LInstr.simple, instrCost]

/-- BRAID simple (no token delta) has zero cost -/
theorem braid_simple_zero_cost : instrCost (LInstr.simple Opcode.BRAID) = 0 := by
  simp [LInstr.simple, instrCost]

/-- MERGE simple (no token delta) has zero cost -/
theorem merge_simple_zero_cost : instrCost (LInstr.simple Opcode.MERGE) = 0 := by
  simp [LInstr.simple, instrCost]

/-- Token delta with opposite signs cancel -/
theorem tokenDelta_cancel :
    instrCost (LInstr.tokenDelta Opcode.BRAID 1) +
    instrCost (LInstr.tokenDelta Opcode.MERGE (-1)) = 0 := by
  simp [LInstr.tokenDelta, instrCost]

/-- FOLD with direction 0 has zero cost -/
theorem fold_zero_direction_neutral :
    instrCost (LInstr.fold 0) = 0 := by
  simp [LInstr.fold, instrCost]

/-- FOLD with direction 1 has cost 1 -/
theorem fold_positive_direction_cost :
    instrCost (LInstr.fold 1) = 1 := by
  simp [LInstr.fold, instrCost]

/-- FOLD with direction -1 has cost 1 -/
theorem fold_negative_direction_cost :
    instrCost (LInstr.fold (-1)) = 1 := by
  simp [LInstr.fold, instrCost]

/-- SEED instruction cost depends on cost argument -/
theorem seed_cost_from_arg (v c : Int) :
    instrCost (LInstr.tokenSet Opcode.SEED v c) = c := by
  simp [LInstr.tokenSet, instrCost]

structure LNALCostAdditiveCert where
  deriving Repr

/-- Verification predicate: LNAL cost has proper structure.

Certifies:
1. BALANCE opcodes have zero cost (neutrality preservation)
2. Control flow opcodes (LOCK, BRAID, MERGE) have zero cost
3. Opposite token deltas cancel exactly
4. FOLD with direction 0 is neutral
5. FOLD with direction ±1 has unit cost
6. SEED cost comes from argument
-/
@[simp] def LNALCostAdditiveCert.verified (_c : LNALCostAdditiveCert) : Prop :=
  -- 1) BALANCE has zero cost
  (instrCost (LInstr.simple Opcode.BALANCE) = 0) ∧
  -- 2) LOCK has zero cost
  (instrCost (LInstr.simple Opcode.LOCK) = 0) ∧
  -- 3) Simple BRAID/MERGE have zero cost
  (instrCost (LInstr.simple Opcode.BRAID) = 0) ∧
  (instrCost (LInstr.simple Opcode.MERGE) = 0) ∧
  -- 4) Opposite token deltas cancel
  (instrCost (LInstr.tokenDelta Opcode.BRAID 1) +
   instrCost (LInstr.tokenDelta Opcode.MERGE (-1)) = 0) ∧
  -- 5) FOLD direction 0 is neutral
  (instrCost (LInstr.fold 0) = 0) ∧
  -- 6) FOLD direction ±1 has unit cost
  (instrCost (LInstr.fold 1) = 1) ∧
  (instrCost (LInstr.fold (-1)) = 1) ∧
  -- 7) SEED cost comes from cost argument
  (∀ v c : Int, instrCost (LInstr.tokenSet Opcode.SEED v c) = c)

/-- Top-level theorem: the LNAL cost certificate verifies. -/
@[simp] theorem LNALCostAdditiveCert.verified_any (c : LNALCostAdditiveCert) :
    LNALCostAdditiveCert.verified c := by
  refine ⟨?balance, ?lock, ?braid, ?merge, ?cancel, ?fold0, ?fold1, ?foldm1, ?seed⟩
  · exact balance_neutral
  · exact lock_zero_cost
  · exact braid_simple_zero_cost
  · exact merge_simple_zero_cost
  · exact tokenDelta_cancel
  · exact fold_zero_direction_neutral
  · exact fold_positive_direction_cost
  · exact fold_negative_direction_cost
  · exact seed_cost_from_arg

end LNALCostAdditive
end Verification
end IndisputableMonolith
