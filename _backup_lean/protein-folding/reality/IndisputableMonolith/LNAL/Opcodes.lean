import Mathlib

namespace IndisputableMonolith
namespace LNAL

/-- Core opcode family for the macrocore ISA (8 primitives). -/
inductive Opcode
| LOCK
| BALANCE
| FOLD
| SEED
| BRAID
| MERGE
| LISTEN
| FLIP
deriving DecidableEq, Repr

/-- Token actions used by primitives that manipulate the ledger/token register. -/
inductive TokenAction
| delta (d : Int)
| set (value : Int) (cost : Int := 0)
deriving DecidableEq, Repr

/-- Balance modes distinguish neutral window resets from full cycle resets. -/
inductive BalanceMode
| window
| cycle
deriving DecidableEq, Repr

/-- Listen modes distinguish observation from vector reset behaviour. -/
inductive ListenMode
| noop
| vectorReset
deriving DecidableEq, Repr

/-- Opcode arguments annotate primitives with macro-level intent. -/
inductive OpcodeArg
| none
| fold (dir : Int)
| token (action : TokenAction)
| balance (mode : BalanceMode)
| listen (mode : ListenMode)
deriving DecidableEq, Repr

/-- Core instruction: primitive opcode plus optional argument metadata. -/
structure LInstr where
  op : Opcode
  arg : OpcodeArg := .none
deriving DecidableEq, Repr

namespace LInstr

/-- Convenience constructor for instructions without additional metadata. -/
@[simp] def simple (op : Opcode) : LInstr := { op := op, arg := .none }

/-- Convenience constructor for fold instructions. -/
@[simp] def fold (dir : Int) : LInstr := { op := Opcode.FOLD, arg := OpcodeArg.fold dir }

/-- Convenience constructor for token-setting instructions (seed/spawn/gc). -/
@[simp] def tokenSet (op : Opcode) (value : Int) (cost : Int := 0) : LInstr :=
  { op := op, arg := OpcodeArg.token (TokenAction.set value cost) }

/-- Convenience constructor for token deltas (give/regive style). -/
@[simp] def tokenDelta (op : Opcode) (delta : Int) : LInstr :=
  { op := op, arg := OpcodeArg.token (TokenAction.delta delta) }

/-- Convenience constructor for balance instructions. -/
@[simp] def balance (mode : BalanceMode) : LInstr :=
  { op := Opcode.BALANCE, arg := OpcodeArg.balance mode }

/-- Convenience constructor for listen instructions. -/
@[simp] def listen (mode : ListenMode) : LInstr :=
  { op := Opcode.LISTEN, arg := OpcodeArg.listen mode }

end LInstr

end LNAL
end IndisputableMonolith
