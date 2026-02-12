import Lake
open Lake DSL

package «hodge» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Hodge» where
  -- add library configuration options here

@[default_target]
lean_exe «ok» where
  root := `Main
