import Mathlib

/-!
# CI: RS-Native Measurement Audit

This audit enforces the v1 measurement spec:

- RS-native measurement modules must not import `IndisputableMonolith.Constants.Codata`
- RS-native measurement modules must not contain CODATA numerals such as:
  - `299792458`
  - `1.054571817e-34`

Run:
- `lake exe rsnative_audit`
-/

namespace CI.RSNativeAudit

open System

def rsnativeRoot : FilePath :=
  FilePath.mk "IndisputableMonolith" / "Measurement" / "RSNative"

def forbiddenSubstrings : List String :=
  [ "IndisputableMonolith.Constants.Codata"
  , "299792458"
  , "1.054571817e-34"
  , "1.054571817"
  ]

partial def collectLeanFiles (root : FilePath) : IO (Array FilePath) := do
  let entries ← root.readDir
  let mut acc : Array FilePath := #[]
  for e in entries do
    let p := e.path
    if (← p.isDir) then
      let sub ← collectLeanFiles p
      acc := acc ++ sub
    else
      match p.extension with
      | some "lean" => acc := acc.push p
      | _ => pure ()
  return acc

def scanFile (p : FilePath) : IO (Array (String × String)) := do
  let s ← IO.FS.readFile p
  let mut hits : Array (String × String) := #[]
  for needle in forbiddenSubstrings do
    if s.contains needle then
      hits := hits.push (p.toString, needle)
  return hits

def run : IO (Array (String × String)) := do
  let files ← collectLeanFiles rsnativeRoot
  let mut hits : Array (String × String) := #[]
  for f in files do
    hits := hits ++ (← scanFile f)
  return hits

def main : IO Unit := do
  let hits ← run
  if hits.isEmpty then
    IO.println "[RSNativeAudit] OK: no forbidden imports/numerals found."
  else
    IO.eprintln "[RSNativeAudit] FAIL: forbidden import/numeral found in RSNative measurement."
    for (file, needle) in hits do
      IO.eprintln s!"  - {file}: contains `{needle}`"
    -- non-zero exit
    IO.Process.exit (1 : UInt8)

end CI.RSNativeAudit

/-! `lean --run` expects a top-level `main`. -/
def main : IO Unit := CI.RSNativeAudit.main


