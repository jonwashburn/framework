import Lake
open Lake DSL

package recognition where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

/-!
Build hygiene:

This repo contains a large number of exploratory / WIP modules. We restrict default
library roots so `lake build` and CI only elaborate the intended, audited surface
unless a specific module/executable is requested explicitly.
-/

lean_lib IndisputableMonolith where
  roots := #[`IndisputableMonolith]

lean_lib URC where
  roots := #[`URC.Minimal]

lean_lib CI where
  roots := #[`CI.Checks, `CI.LNALTests, `CI.LNALCliSmoke]

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

lean_exe exclusivity_check {
  root := `CI.ExclusivityCheck
}

lean_exe cpm_audit {
  root := `IndisputableMonolith.CPM.AuditMain
}

/-! ## RSNative measurement audits -/

lean_exe rsnative_audit {
  root := `CI.RSNativeAudit
}

lean_exe rsnative_protocol_audit {
  root := `CI.RSNativeProtocolAudit
}

/-! ## Certificate of Inevitability -/

lean_exe inevitability_cert {
  root := `IndisputableMonolith.Verification.MeaningCompiler.CertificateMain
}
