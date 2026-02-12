/-!
# RRF JSON Audit Tool

CLI tool that consumes a trace JSON and emits an RRF invariants report.

Usage:
  lake exe rrf_audit <trace.json>

Output:
  JSON report to stdout
-/

import IndisputableMonolith.RRF.Adapters
import Lean.Data.Json.Parser

open IndisputableMonolith.RRF.Adapters
open Lean (Json ToJson)

/-- Parse a simple CPM trace from JSON (minimal schema). -/
def parseCPMTraceFromJson (json : Json) : Option CPMTrace := do
  let obj ← json.getObj?
  let sequence ← (obj.find? "sequence").bind (·.getStr?)
  let finalRMSD := (obj.find? "final_rmsd").bind (·.getNum?) |>.map (·.toFloat)
  -- Simplified: just return minimal trace
  some {
    sequence := sequence
    moves := []
    phases := []
    temperatures := []
    finalRMSD := finalRMSD
  }

/-- Generate a report from JSON input. -/
def auditFromJson (input : String) (traceId : String) : IO String := do
  match Json.parse input with
  | .error e => return s!"JSON parse error: {e}"
  | .ok json =>
    match parseCPMTraceFromJson json with
    | none => return "Could not parse trace structure"
    | some trace =>
      let report := generateCPMReport trace traceId
      return (ToJson.toJson report).pretty

/-- Main entry point. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let content ← IO.FS.readFile path
    let traceId := System.FilePath.fileName path |>.getD "unknown"
    let report ← auditFromJson content traceId
    IO.println report
    return 0
  | _ =>
    IO.eprintln "Usage: rrf_audit <trace.json>"
    return 1
