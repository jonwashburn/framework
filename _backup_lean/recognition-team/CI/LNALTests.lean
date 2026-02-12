import Mathlib
import IndisputableMonolith.LNAL.Parser
import IndisputableMonolith.LNAL.Compiler

open IndisputableMonolith
open IndisputableMonolith.LNAL

namespace CI

private def mkCode (ops : List LInstr) : Array LInstr := Array.mk ops

private def reportMsg (rep : CompileReport) : String :=
  if rep.ok then "ok" else s!"fail: {String.intercalate "; " rep.errors}"

def main : IO UInt32 := do
  -- Positive sample: includes BALANCE in first 8, VECTOR_EQ within 1024, no double LISTEN,
  -- parity respected and cost bounded in a short run, GC_SEED after SEED, at least one FLIP.
  let okOps : List LInstr :=
    [ LInstr.tokenSet Opcode.SEED 1 1
    , LInstr.fold 1
    , LInstr.tokenDelta Opcode.BRAID 1
    , LInstr.fold (-1)
    , LInstr.tokenDelta Opcode.MERGE (-1)
    , LInstr.listen ListenMode.noop
    , LInstr.simple Opcode.BRAID
    , LInstr.balance BalanceMode.window
    , LInstr.simple Opcode.FLIP
    , LInstr.listen ListenMode.vectorReset
    , LInstr.balance BalanceMode.cycle
    , LInstr.tokenSet Opcode.SEED 0 0
    ]
  let okRep := staticChecks (mkCode okOps)
  if ¬ okRep.ok then
    IO.eprintln s!"[LNALTests][FAIL] positive sample: {reportMsg okRep}"
    return 1

  -- Negative: missing BALANCE in first 8
  let negNoBal : List LInstr :=
    [ LInstr.tokenSet Opcode.SEED 1 1
    , LInstr.fold 1, LInstr.tokenDelta Opcode.BRAID 1, LInstr.fold (-1), LInstr.tokenDelta Opcode.MERGE (-1)
    , LInstr.listen ListenMode.noop, LInstr.simple Opcode.BRAID, LInstr.fold 1
    , LInstr.listen ListenMode.vectorReset
    ]
  let repNoBal := staticChecks (mkCode negNoBal)
  if repNoBal.ok then
    IO.eprintln s!"[LNALTests][FAIL] expected BALANCE/8 failure, got ok"
    return 2

  -- Negative: double LISTEN stall
  let negDoubleListen : List LInstr :=
    [ LInstr.listen ListenMode.noop, LInstr.listen ListenMode.noop,
      LInstr.balance BalanceMode.window, LInstr.listen ListenMode.vectorReset ]
  let repDL := staticChecks (mkCode negDoubleListen)
  if repDL.ok then
    IO.eprintln s!"[LNALTests][FAIL] expected double LISTEN failure, got ok"
    return 3

  -- Negative: parity blow-up (too many GIVE without REGIVE)
  let negParity : List LInstr :=
    [ LInstr.tokenDelta Opcode.BRAID 1,
      LInstr.tokenDelta Opcode.BRAID 1,
      LInstr.tokenDelta Opcode.BRAID 1,
      LInstr.balance BalanceMode.window,
      LInstr.listen ListenMode.vectorReset ]
  let repParity := staticChecks (mkCode negParity)
  if repParity.ok then
    IO.eprintln s!"[LNALTests][FAIL] expected token parity failure, got ok"
    return 4

  -- Negative: cost ceiling exceeded (net GIVE > 4)
  let negCost : List LInstr :=
    [ LInstr.tokenDelta Opcode.BRAID 1,
      LInstr.tokenDelta Opcode.BRAID 1,
      LInstr.tokenDelta Opcode.BRAID 1,
      LInstr.tokenDelta Opcode.BRAID 1,
      LInstr.tokenDelta Opcode.BRAID 1,
      LInstr.balance BalanceMode.window,
      LInstr.listen ListenMode.vectorReset ]
  let repCost := staticChecks (mkCode negCost)
  if repCost.ok then
    IO.eprintln s!"[LNALTests][FAIL] expected cost ceiling failure, got ok"
    return 5

  -- Negative: SEED without GC_SEED within window
  let negGCSeed : List LInstr :=
    [ LInstr.tokenSet Opcode.SEED 1 1 ] ++ List.replicate 30 (LInstr.balance BalanceMode.window)
  let repGC := staticChecks (mkCode negGCSeed)
  if repGC.ok then
    IO.eprintln s!"[LNALTests][FAIL] expected SEED/GC_SEED window failure, got ok"
    return 6

  -- Parser round-trip on the positive sample
  let codeArr := mkCode okOps
  let ser := serializeProgram codeArr
  match parseProgram ser with
  | .error e =>
      IO.eprintln s!"[LNALTests][FAIL] round-trip parse error: {repr e}"
      return 7
  | .ok code' =>
      if code' ≠ codeArr then
        IO.eprintln s!"[LNALTests][FAIL] round-trip mismatch: expected {codeArr.size}, got {code'.size}"
        return 8

  IO.println "[LNALTests] OK"
  return 0

end CI
