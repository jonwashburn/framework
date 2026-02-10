import Std
import Lean

/-!
## Opaque audit (source-level)

`#print axioms` only reports explicit axioms in a proof term. It does **not** report hidden
assumptions introduced via `opaque` constants.

This file performs a **source-level** audit: it scans the `Hodge/` directory for lines that
begin with `opaque` (after trimming leading whitespace) and prints them with file+line numbers.

Run with:

```bash
lake env lean Hodge/Utils/AuditOpaque.lean
```

For broader “faithfulness” checks (axioms, sorries, semantic stubs), see:
`scripts/audit_faithfulness.sh`.
-/

open Lean

namespace HodgeAudit

def collectLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  -- We intentionally use the system `find` command for portability across Lean/Std versions
  -- (Lean core does not expose a stable directory-walk API across toolchains).
  let out ← IO.Process.output {
    cmd := "find"
    args := #[
      dir.toString,
      "-type", "f",
      "-name", "*.lean",
      "-print"
    ]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"find failed (exit {out.exitCode}): {out.stderr}"
  let paths := out.stdout.splitOn "\n" |>.filter (fun s => s != "")
  return paths.toArray.map System.FilePath.mk

def isOpaqueLine (line : String) : Bool :=
  line.trimAsciiStart.toString.startsWith "opaque "

def formatHit (path : System.FilePath) (lineNo : Nat) (line : String) : String :=
  s!"{path}:{lineNo}: {line}"

end HodgeAudit

open HodgeAudit

#eval show IO Unit from do
  let root : System.FilePath := "Hodge"
  let files ← collectLeanFiles root
  let mut hits : Array String := #[]
  for f in files do
    let content ← IO.FS.readFile f
    let mut lineNo : Nat := 1
    for line in content.splitOn "\n" do
      if isOpaqueLine line then
        hits := hits.push (formatHit f lineNo line)
      lineNo := lineNo + 1

  IO.println s!"[AuditOpaque] scanned {files.size} Lean files under `{root}`"
  IO.println s!"[AuditOpaque] found {hits.size} `opaque` declaration line(s)"
  for h in hits do
    IO.println h
