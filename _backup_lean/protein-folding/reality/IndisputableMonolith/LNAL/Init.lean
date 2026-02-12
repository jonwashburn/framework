import Mathlib
import IndisputableMonolith.LNAL.Registers
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.VM

namespace IndisputableMonolith
namespace LNAL

/-- Typeclass for domain objects that can be initialized into LNAL registers. -/
class LedgerInit (α : Type) where
  toReg   : α → Reg6 × Aux5
  seedOps : α → List Opcode := fun _ => []

/-- Helper to lift seed opcodes into LInstr. -/
def LedgerInit.seedInstrs {α} [LedgerInit α] (a : α) : List LInstr :=
  (LedgerInit.seedOps a).map (fun op => LInstr.simple op)

/-! Identity instances -/

/-- Identity instance for already prepared `(Reg6 × Aux5)` pairs. -/
instance : LedgerInit (Reg6 × Aux5) where
  toReg x := x
  seedOps _ := []

/-! Minimal protein stub and instance

This is a light scaffolding that demonstrates how a domain type would
map into the Reg6 × Aux5 schema without bringing external dependencies.
-/

structure Residue where
  nuPhiEst : Int := 0
  ellEst   : Int := 0
deriving Repr, DecidableEq

instance : LedgerInit Residue where
  toReg r :=
    let r6 := { Reg6.zero with nuPhi := r.nuPhiEst, ell := r.ellEst }
    (r6, Aux5.zero)
  seedOps _ := []

end LNAL
end IndisputableMonolith
