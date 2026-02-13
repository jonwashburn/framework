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

lean_exe core_audit {
  root := `IndisputableMonolith.URCAdapters.CoreAuditMain
}

lean_exe ok {
  root := `IndisputableMonolith.OKMini
}

lean_exe audit {
  root := `IndisputableMonolith.URCAdapters.Audit
}

lean_exe cpm_audit {
  root := `IndisputableMonolith.CPM.AuditMain
}

/-! ## Certificate of Inevitability -/

lean_exe inevitability_cert {
  root := `IndisputableMonolith.Verification.MeaningCompiler.CertificateMain
}
