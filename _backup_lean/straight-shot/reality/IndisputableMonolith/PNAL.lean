import IndisputableMonolith.PNAL.Syntax
import IndisputableMonolith.PNAL.Compiler

/-!
# PNAL Module

Protein Native Assembly Language (PNAL) - a high-level, typed language
for expressing protein folding as programs that compile to LNAL.

## Components

- **Syntax**: AST definition for PNAL instructions
- **Compiler**: PNAL → LNAL translation with invariant preservation

## Usage Example

```lean
open PNAL

-- Define a simple folding program
def myProtein : PNALProgram :=
  let h : 10 ≤ 20 := by norm_num
  ⟨[
    PNALInstr.nucleateHelix 10 20 h,
    PNALInstr.listenPhase,
    PNALInstr.setContact 10 20,
    PNALInstr.listenPhase,
    PNALInstr.assertNoClash
  ], some "Example protein"⟩

-- Compile to LNAL
#eval compileToLNAL myProtein
```

## Status

- ✓ Syntax module complete
- ✓ Basic compiler complete
- ⏳ Type checker: TODO
- ⏳ Optimization passes: TODO
- ⏳ Full invariant proofs: TODO

## References

- `Protein Folding as Phase Recognition.tex`: Full specification
- `tools/pnal/README.md`: Language design documentation
-/
