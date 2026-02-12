import IndisputableMonolith.LightLanguage.LNAL.Core
import IndisputableMonolith.LightLanguage.LNAL.Operators
import IndisputableMonolith.LightLanguage.LNAL.NormalForm

/-!
# LNAL Aggregator Module

This module re-exports the LNAL (Light Numeric Assembly Language) subsystem.

## Module Structure

- `LNAL/Core.lean`: **Canonical definitions** (single source of truth)
  - `Op` / `LNALOp`: The 5 primitive operators
  - `Sequence` / `LNALSequence`: Operator sequences
  - `LedgerState`: Execution state
  - `LegalTriad`: BRAID validity predicate

- `LNAL/Operators.lean`: Operator properties and invariants

- `LNAL/NormalForm.lean`: Normal form reduction

- `LNAL/Execution.lean`: Full execution semantics (optional)

## Usage

Import this module to get all LNAL functionality:

```lean
import IndisputableMonolith.LightLanguage.LNAL
```

For just the core types, import directly:

```lean
import IndisputableMonolith.LightLanguage.LNAL.Core
```
-/

namespace IndisputableMonolith.LightLanguage.LNAL

-- Core types are already in this namespace from Core.lean
-- No need to re-export

end IndisputableMonolith.LightLanguage.LNAL
