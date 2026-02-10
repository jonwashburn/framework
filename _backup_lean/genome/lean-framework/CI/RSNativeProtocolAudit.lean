import IndisputableMonolith.Measurement.RSNative

/-!
# CI: RS-Native Protocol Hygiene Audit

This audit checks the measurement spec hygiene rules that are *hard* to see from import greps:

- every protocol name must be non-empty
- any protocol with `status = hypothesis` or `status = scaffold` must have:
  - at least one assumption
  - at least one falsifier

Run:
- `lake env lean --run CI/RSNativeProtocolAudit.lean`
- (optional) `lake exe rsnative_protocol_audit` (if wired in `lakefile.lean`)
-/

namespace CI.RSNativeProtocolAudit

open IndisputableMonolith
open IndisputableMonolith.Measurement
open IndisputableMonolith.Measurement.RSNative

def protocols : List Protocol :=
  [ Catalog.Ledger.protocol_recognitionCost
  , Catalog.Ledger.protocol_netSkew
  , Catalog.Ledger.protocol_reciprocitySkewAbs
  , Catalog.Ledger.protocol_totalZ
  , Catalog.Ledger.protocol_pathAction
  , Catalog.VoxelMeaning.protocol_totalEnergy
  , Catalog.VoxelMeaning.protocol_modeEnergy
  , Catalog.Ethics.protocol_skew
  , Catalog.Ethics.protocol_absSkew
  , Catalog.Ethics.protocol_wiseChoice
  , Catalog.Ethics.protocol_prudentChoice
  , Catalog.Qualia.protocol_qualiaModeOfWToken
  , Catalog.Qualia.protocol_qualiaEnergy
  , Adapters.StreamToLedger.protocol
  , Adapters.VoxelToWToken.protocol
  ]

def failures : List Protocol :=
  protocols.filter (fun p => !(Protocol.hygienicBool p))

def main : IO Unit := do
  if failures.isEmpty then
    IO.println "[RSNativeProtocolAudit] OK: protocol hygiene checks passed."
  else
    IO.eprintln "[RSNativeProtocolAudit] FAIL: protocol hygiene checks failed."
    for p in failures do
      IO.eprintln s!"  - {p.name} (status={reprStr p.status})"
      if p.name.isEmpty then
        IO.eprintln "      • empty name"
      if p.status = .hypothesis ∨ p.status = .scaffold then
        if p.assumptions.isEmpty then
          IO.eprintln "      • missing assumptions"
        if p.falsifiers.isEmpty then
          IO.eprintln "      • missing falsifiers"
    IO.Process.exit (1 : UInt8)

end CI.RSNativeProtocolAudit

/-! `lean --run` expects a top-level `main`. -/
def main : IO Unit := CI.RSNativeProtocolAudit.main


