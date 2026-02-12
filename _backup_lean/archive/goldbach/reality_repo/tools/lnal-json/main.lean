import Mathlib
import Lean
import IndisputableMonolith.LNAL.Parser
import IndisputableMonolith.URCAdapters.LNALReports

open IndisputableMonolith
open IndisputableMonolith.LNAL
open IndisputableMonolith.URCAdapters

structure Args where
  input : String := ""
  deriving Repr

def parseArgs (argv : List String) : Except String Args :=
  match argv with
  | [file] => .ok { input := file }
  | _      => .error "Usage: lake env lean --run tools/lnal-json/main.lean <file.lnal>"

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error e => IO.eprintln e; return 1
  | .ok cfg =>
      let src ← IO.FS.readFile cfg.input
      -- Emit a JSON object with all per-source certs
      let j := "{\n"
        ++ "  \"invariants\": " ++ lnal_invariants_report_json src ++ ",\n"
        ++ "  \"compiler\": " ++ compiler_checks_report_json src ++ ",\n"
        ++ "  \"opcode_soundness\": " ++ opcode_soundness_report_json src ++ ",\n"
        ++ "  \"schedule_neutrality\": " ++ schedule_neutrality_report_json src ++ ",\n"
        ++ "  \"cost_ceiling\": " ++ cost_ceiling_report_json src ++ ",\n"
        ++ "  \"su3_mask\": " ++ su3_mask_report_json src ++ "\n"
        ++ "}\n"
      IO.print j
      return 0
