import IndisputableMonolith.LNAL.Opcodes

namespace IndisputableMonolith
namespace LNAL

/-! Cost Assignment to Opcodes -/

/-- J-cost rate for a primitive instruction (dimensionless units). -/
def instrCost : LInstr → Int
  | ⟨Opcode.FOLD, OpcodeArg.fold dir⟩ => if dir = 0 then 0 else 1
  | ⟨Opcode.FOLD, _⟩ => 1
  | ⟨Opcode.BRAID, OpcodeArg.token (TokenAction.delta d)⟩ => d
  | ⟨Opcode.MERGE, OpcodeArg.token (TokenAction.delta d)⟩ => d
  | ⟨Opcode.SEED, OpcodeArg.token (TokenAction.set _ cost)⟩ => cost
  | _ => 0

end LNAL
end IndisputableMonolith
