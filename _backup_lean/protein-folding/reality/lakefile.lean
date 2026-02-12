import Lake
open Lake DSL

package recognition

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib IndisputableMonolith
lean_lib URC

lean_exe ci_checks {
  root := `CI.Checks
}

lean_exe core_audit {
  root := `IndisputableMonolith.URCAdapters.CoreAuditMain
}

lean_exe ok {
  root := `IndisputableMonolith.OKMini
}

lean_exe ci {
  root := `CI.Checks
}

lean_exe audit {
  root := `IndisputableMonolith.URCAdapters.Audit
}

lean_exe qg_harness {
  root := `CI.QGHarness
}
