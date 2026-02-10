import IndisputableMonolith.LNAL.Parser
import IndisputableMonolith.LNAL.Compiler

namespace IndisputableMonolith
namespace LNAL

/-!
# LNAL Parser Examples and Tests

Demonstrates macro expansion, label support, and error handling.
-/

/-- Example 1: Basic opcode sequence with labels -/
def example1 : String :=
"start:
  LOCK
  BALANCE
  FOLD
loop:
  GIVE
  LISTEN
  BALANCE
  REGIVE
  BALANCE
  FLIP"

/-- Example 2: Macro expansion -/
def example2 : String :=
"# Photon emission sequence
init:
  SEED
  PHOTON_EMIT  # Expands to: FOLD, GIVE, UNFOLD
  BALANCE

cleanup:
  DIAMOND_CELL  # Expands to: LOCK, BALANCE, HARDEN
  GC_SEED
  VECTOR_EQ"

/-- Example 3: Eight-tick neutral window -/
def example3 : String :=
"# Eight-tick window with BALANCE at boundary
tick0: LOCK
tick1: FOLD
tick2: GIVE
tick3: UNFOLD
tick4: REGIVE
tick5: LISTEN
tick6: BRAID
tick7: BALANCE  # Window neutrality enforced

# Repeat pattern
tick8: FOLD
tick9: UNFOLD
tick10: LISTEN
tick11: BRAID
tick12: SEED
tick13: SPAWN
tick14: MERGE
tick15: BALANCE"

/-- Example 4: Full breath cycle (1024 ticks) -/
def example4 : String :=
"# Minimal breath with FLIP at midpoint
breath_start:
  SEED_SPAWN  # Macro: SEED, SPAWN

main_loop:
  FOLD
  BALANCE
  UNFOLD
  BALANCE
  LISTEN
  BALANCE
  BRAID
  BALANCE  # Complete 8-tick window

  # ... repeat 127 more times to reach tick 512 ...

flip_point:
  FLIP  # Tick 511 (breathPeriod/2 - 1 = 512/2 - 1 = 511)

post_flip:
  BALANCE
  # ... continue to tick 1023 ...

breath_end:
  VECTOR_EQ  # Reset cycle sum at breath boundary
  CYCLE"

/-- Example 5: Error case - unknown opcode -/
def exampleError1 : String :=
"LOCK
BALANCE
UNKNOWN_OP  # Should trigger parse error
FOLD"

/-- Example 6: Error case - unknown macro -/
def exampleError2 : String :=
"SEED
FAKE_MACRO  # Should trigger unknown macro error
BALANCE"

/-! Test Harness -/

/-- Test parsing success -/
def testParse (src : String) (name : String := "test") : IO Unit := do
  match parseProgram src with
  | .ok code =>
      IO.println s!"✓ {name}: parsed {code.size} instructions"
      let stats := programStats code
      IO.println s!"  Stats: {stats.totalInstructions} total, " ++
                 s!"BALANCE={stats.opcodeCount Opcode.BALANCE}, " ++
                 s!"FLIP={stats.opcodeCount Opcode.FLIP}"
  | .error e =>
      IO.println s!"✗ {name}: parse error: {repr e}"

/-- Test expected error -/
def testParseError (src : String) (name : String := "error_test") : IO Unit := do
  match parseProgram src with
  | .ok _ =>
      IO.println s!"✗ {name}: expected error but succeeded"
  | .error e =>
      IO.println s!"✓ {name}: caught expected error: {repr e}"

/-- Run all tests -/
def runParserTests : IO Unit := do
  IO.println "LNAL Parser Test Suite"
  IO.println "======================"
  IO.println ""

  testParse example1 "example1_basic"
  testParse example2 "example2_macros"
  testParse example3 "example3_eight_tick"
  testParse example4 "example4_breath"

  IO.println ""
  IO.println "Error Tests:"
  testParseError exampleError1 "unknown_opcode"
  testParseError exampleError2 "unknown_macro"

  IO.println ""
  IO.println "Compiler Integration Tests:"

  -- Test compilation with static checks
  let (report, prog) := compile example2
  if report.ok then
    IO.println s!"✓ Compiler: static checks passed"
  else
    IO.println s!"✗ Compiler: errors = {report.errors}"

  IO.println ""
  IO.println "Parser tests complete."

/-- Macro expansion test -/
example : expandMacro "PHOTON_EMIT" =
    some (Array.mk [LInstr.fold 1, LInstr.tokenDelta Opcode.BRAID 1, LInstr.fold (-1)]) := rfl

/-- Token expansion test -/
example : expandToken "BALANCE" = some #[LInstr.balance BalanceMode.window] := rfl

/-- Unknown token returns none -/
example : expandToken "INVALID" = none := rfl

end LNAL
end IndisputableMonolith
