import Lake
open Lake DSL

package recognition

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib IndisputableMonolith
lean_lib URC
lean_lib CI

lean_exe ci_checks {
  root := `CI.Checks
}

lean_exe ci {
  root := `CI.Checks
}

-- Note: Some executables have been removed as they depend on 
-- modules not included in this distribution.
