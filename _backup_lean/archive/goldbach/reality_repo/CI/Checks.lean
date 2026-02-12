import IndisputableMonolith.URCAdapters.Reports
import CI.LNALTests
import CI.LNALCliSmoke
import CI.ExclusivityCheck

/‑!
  Minimal CI smoke: print consolidated certificates_manifest to ensure
  all certificate modules elaborate. Keep lightweight.
‑/

def main : IO Unit := do
  -- Run LNAL tests (non-fatal; print failures before manifest)
  let rc ← CI.main
  if rc ≠ 0 then
    IO.eprintln s!"[CI] LNALTests failed with code {rc}"
  -- Run CLI smoke (non-fatal)
  let rc2 ← CI_CLI.main
  if rc2 ≠ 0 then
    IO.eprintln s!"[CI] LNALCliSmoke failed with code {rc2}"
  -- Run exclusivity check
  IO.println ""
  CI.ExclusivityCheck.main
  IO.println ""
  let manifest := IndisputableMonolith.URCAdapters.certificates_manifest
  IO.println manifest
