import Mathlib
import IndisputableMonolith.LNAL.Opcodes

namespace IndisputableMonolith
namespace LNAL

/-!
# LNAL.InstrCost

Minimal cost assignment for the LNAL instruction set.

This file exists to avoid import cycles between:
- the executable VM (`LNAL/VM.lean`), and
- higher-level cost/certificate proofs (`LNAL/CostProofs.lean`) that may depend on
  invariants and other theory.

In particular, `LNAL/VM.lean` needs *only* the primitive `instrCost` function.
-/

/-- J-cost rate for a primitive instruction (dimensionless units).

This is intentionally small and local: the VM uses it for bookkeeping;
deeper theorems about cost/uniqueness live elsewhere. -/
def instrCost : LInstr → Int
  | ⟨Opcode.FOLD, OpcodeArg.fold dir⟩ => if dir = 0 then 0 else 1
  | ⟨Opcode.FOLD, _⟩ => 1
  | ⟨Opcode.BRAID, OpcodeArg.token (TokenAction.delta d)⟩ => d
  | ⟨Opcode.MERGE, OpcodeArg.token (TokenAction.delta d)⟩ => d
  | ⟨Opcode.SEED, OpcodeArg.token (TokenAction.set _ cost)⟩ => cost
  | _ => 0

end LNAL
end IndisputableMonolith
