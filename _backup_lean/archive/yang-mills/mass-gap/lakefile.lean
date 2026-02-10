import Lake
open Lake DSL

-- Configure the Lean toolchain
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0-rc1"

package ym where
  -- Lean compiler options
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- YM Framework (Yang-Mills)
lean_lib YMFramework where  
  roots := #[`YMFramework]

-- Executable for verification
lean_exe ym where
  root := `Main
