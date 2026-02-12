import IndisputableMonolith.LNAL.Parser
import IndisputableMonolith.LNAL.Compiler
import IndisputableMonolith.LNAL.Backend.Verilog

namespace LNAL.Compiler

/-!
# LNAL Standalone Compiler

Command-line tool for compiling LNAL assembly to bytecode or Verilog.

## Usage

```bash
# Compile to bytecode
lnal-compile input.lnal -o output.bytecode

# Compile to Verilog (FPGA)
lnal-compile input.lnal --target fpga -o output.v

# Check only (static analysis)
lnal-compile input.lnal --check-only

# Show statistics
lnal-compile input.lnal --stats

# Pretty-print (formatted assembly)
lnal-compile input.lnal --pretty
```

## Exit Codes

- 0: Success
- 1: Parse error
- 2: Static check failure
- 3: File I/O error
- 4: Invalid arguments
-/

/-- Compiler configuration -/
structure CompilerConfig where
  inputFile : String
  outputFile : Option String := none
  target : String := "bytecode"  -- "bytecode" | "fpga" | "check"
  showStats : Bool := false
  prettyPrint : Bool := false
  verbose : Bool := false
  optimize : Bool := true
  consentGate : Bool := false
deriving Repr

private def previewNatArray (arr : Array Nat) (limit : Nat := 4) : String :=
  let previewVals := (arr.toList.take limit).map (fun n => toString n)
  let body := String.intercalate ", " previewVals
  if previewVals.isEmpty then "[]"
  else
    let ellipsis := if arr.size > previewVals.length then ", …" else ""
    "[" ++ body ++ ellipsis ++ "]"

/-- Parse command-line arguments -/
def parseArgs (args : List String) : Except String CompilerConfig :=
  let rec loop (args : List String) (cfg : CompilerConfig) : Except String CompilerConfig :=
    match args with
    | [] => .ok cfg
    | "-o" :: file :: rest => loop rest { cfg with outputFile := some file }
    | "--output" :: file :: rest => loop rest { cfg with outputFile := some file }
    | "--target" :: tgt :: rest => loop rest { cfg with target := tgt }
    | "--check-only" :: rest => loop rest { cfg with target := "check" }
    | "--stats" :: rest => loop rest { cfg with showStats := true }
    | "--pretty" :: rest => loop rest { cfg with prettyPrint := true }
    | "-v" :: rest => loop rest { cfg with verbose := true }
    | "--verbose" :: rest => loop rest { cfg with verbose := true }
    | "--no-optimize" :: rest => loop rest { cfg with optimize := false }
    | "--consent-gate" :: rest => loop rest { cfg with consentGate := true }
    | file :: rest =>
        if file.startsWith "-" then
          .error s!"Unknown option: {file}"
        else if cfg.inputFile.isEmpty then
          loop rest { cfg with inputFile := file }
        else
          .error s!"Multiple input files not supported"

  loop args { inputFile := "" }

/-- Main compiler entry point -/
def compileMain (cfg : CompilerConfig) : IO UInt32 := do
  -- Read input file
  let src ← IO.FS.readFile cfg.inputFile

  if cfg.verbose then
    IO.println s!"Compiling {cfg.inputFile}..."

  -- Parse
  match IndisputableMonolith.LNAL.parseProgramFull src with
  | .error e =>
      IO.eprintln s!"Parse error: {repr e}"
      return 1

  | .ok out =>
      let code := out.code
      let phi := out.phi
      if cfg.verbose then
        IO.println s!"✓ Parsed {code.size} instructions"
        IO.println s!"  φ-literals: {phi.literals.size}"

      -- Static checks
      let report := IndisputableMonolith.LNAL.staticChecks code phi out.packets cfg.consentGate

      if ¬report.ok then
        IO.eprintln "Static check failures:"
        for err in report.errors do
          IO.eprintln s!"  ✗ {err}"
        return 2

      if cfg.verbose then
        IO.println "✓ Static checks passed"
        IO.println s!"  J-monotone ΔJ preview: {previewNatArray report.jMonotone.deltaJ}"
        if ¬report.warnings.isEmpty then
          IO.println "  Warnings:"
          for warn in report.warnings do
            IO.println s!"    ⚠ {warn}"
        if phi.literals.size > 0 then
          let samples := phi.literals.toList.take 3
          for lit in samples do
            let summary := IndisputableMonolith.LNAL.PhiIR.PhiLiteral.summary lit
            IO.println s!"    φ-literal {summary}"
        if ¬report.commitWindows.isEmpty then
          let commits := report.commitWindows.map (fun w => s!"(window {w.window}, ΔJ={w.deltaJ})")
          IO.println s!"  COMMIT windows: {String.intercalate ", " commits}"
        if ¬report.phiPackets.packets.isEmpty then
          let neutralStatus := if report.phiPackets.allNeutral then "all neutral" else "violations"
          IO.println s!"  φ-IR packets: {report.phiPackets.packets.length} ({neutralStatus})"
          let samples := report.phiPackets.packets.take 2
          for pkt in samples do
            IO.println s!"    window {pkt.window} gray={pkt.gray} len={pkt.length} netΔ={pkt.netDelta} balances={pkt.balanceCount}"
        if ¬report.jGreedy.isEmpty then
          IO.println "  J-greedy schedule (top windows):"
          let samples := report.jGreedy.take 3
          for win in samples do
            IO.println s!"    window {win.window} gray={win.gray} predictedΔJ={win.predictedDelta} actualΔJ={win.actualDelta}"
        if ¬report.progressWitnesses.isEmpty then
          let stuck := report.progressWitnesses.filter (fun w => w.status = LNAL.ProgressStatus.stuck)
          if ¬stuck.isEmpty then
            let stuckStr := String.intercalate ", " (stuck.map (fun w => s!"{w.window}"))
            IO.println s!"  Stuck windows (ΔJ=0): {stuckStr}"
          let progress := report.progressWitnesses.filter (fun w => w.status = LNAL.ProgressStatus.progress)
          if ¬progress.isEmpty then
            let preview := progress.take 3
            IO.println "  Progress windows (ΔJ witnesses):"
            for w in preview do
              IO.println s!"    window {w.window} {w.reason}"
        if cfg.consentGate then
          if report.consent.ok then
            IO.println "  ConsentDerivative gate: OK"
          else
            IO.println s!"  ConsentDerivative violations at steps {String.intercalate ", " (report.consent.violations.map (fun n => ToString.toString n))}"

      -- Show stats if requested
      if cfg.showStats then
        let stats := IndisputableMonolith.LNAL.programStats code
        IO.println s!"Statistics:"
        IO.println s!"  Total instructions: {stats.totalInstructions}"
        IO.println s!"  BALANCE count: {stats.opcodeCount Opcode.BALANCE}"
        IO.println s!"  FOLD count: {stats.opcodeCount Opcode.FOLD}"
        IO.println s!"  BRAID count: {stats.opcodeCount Opcode.BRAID}"
        IO.println s!"  MERGE count: {stats.opcodeCount Opcode.MERGE}"
        IO.println s!"  Has FLIP: {stats.hasFlip}"
        IO.println s!"  Has VECTOR_EQ: {stats.hasVectorEq}"
        IO.println s!"  J-monotone ΔJ preview: {previewNatArray report.jMonotone.deltaJ}"

      -- Pretty print if requested
      if cfg.prettyPrint then
        IO.println (IndisputableMonolith.LNAL.prettyPrint code)
        return 0

      -- Check-only mode
      if cfg.target = "check" then
        IO.println "✓ All checks passed"
        return 0

      -- Generate output based on target
      match cfg.target with
      | "bytecode" =>
          -- Simple bytecode format (future: binary encoding)
          if let some outFile := cfg.outputFile then
            let bytecode := code.foldl (fun acc i =>
              acc ++ s!"{repr i.op}\n") ""
            IO.FS.writeFile outFile bytecode
            IO.println s!"✓ Bytecode written to {outFile}"
          else
            IO.eprintln "Error: -o required for bytecode target"
            return 4
          return 0

      | "fpga" =>
          let opts : IndisputableMonolith.LNAL.Backend.VerilogOptions := {
            moduleName := "lnal_core",
            generateTestbench := true,
            generateTCL := true,
            multiCore := false
          }

          let bundle := IndisputableMonolith.LNAL.Backend.compileVerilogBundle code opts

          if let some outDir := cfg.outputFile then
            IndisputableMonolith.LNAL.Backend.writeVerilogBundle bundle outDir
            IO.println s!"✓ Verilog bundle written to {outDir}/"
          else
            IO.eprintln "Error: -o required for FPGA target (directory path)"
            return 4
          return 0

      | _ =>
          IO.eprintln s!"Unknown target: {cfg.target}"
          return 4

/-- Show help message -/
def showHelp : IO Unit := do
  IO.println "LNAL Compiler - Light-Native Assembly Language"
  IO.println ""
  IO.println "Usage: lnal-compile [options] <input.lnal>"
  IO.println ""
  IO.println "Options:"
  IO.println "  -o, --output FILE       Output file/directory"
  IO.println "  --target TARGET         Target: bytecode | fpga | check"
  IO.println "  --check-only            Run static checks only (no output)"
  IO.println "  --stats                 Show program statistics"
  IO.println "  --pretty                Pretty-print program"
  IO.println "  -v, --verbose           Verbose output"
  IO.println "  --no-optimize           Disable optimizations"
  IO.println "  --consent-gate          Enable ConsentDerivative static/runtime gate"
  IO.println ""
  IO.println "Examples:"
  IO.println "  lnal-compile program.lnal -o program.bytecode"
  IO.println "  lnal-compile program.lnal --target fpga -o verilog_out/"
  IO.println "  lnal-compile program.lnal --check-only"
  IO.println ""
  IO.println "Exit codes:"
  IO.println "  0: Success"
  IO.println "  1: Parse error"
  IO.println "  2: Static check failure"
  IO.println "  3: File I/O error"
  IO.println "  4: Invalid arguments"

/-- Main entry point -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty || args.contains "-h" || args.contains "--help" then
    showHelp
    return 0

  match parseArgs args with
  | .error msg =>
      IO.eprintln s!"Argument error: {msg}"
      showHelp
      return 4

  | .ok cfg =>
      if cfg.inputFile.isEmpty then
        IO.eprintln "Error: No input file specified"
        showHelp
        return 4

      compileMain cfg

end LNAL.Compiler
