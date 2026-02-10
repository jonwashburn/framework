import Mathlib
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.VM

namespace IndisputableMonolith
namespace LNAL

/-!
Thin aggregator module for LNAL.

This module re-exports the 16-opcode LNAL instruction set (`Opcode`) and
the typed VM (`LInstr`, `LProgram`, `LState`, `lStep`, `breathPeriod`) from
`IndisputableMonolith.LNAL.{Opcodes,VM}`.

The legacy generic ALU VM has been removed to avoid divergence from the
LNAL specification.
-/

-- Re-export selected identifiers for convenience
-- (No explicit `export` needed: importing `Opcodes` and `VM` already provides
-- `IndisputableMonolith.LNAL.breathPeriod`.)

end LNAL
end IndisputableMonolith
