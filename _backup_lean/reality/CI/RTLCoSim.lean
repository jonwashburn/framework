import Mathlib
import IndisputableMonolith.LNAL.Parser
import IndisputableMonolith.LNAL.VM
import IndisputableMonolith.LNAL.JBudget
import IndisputableMonolith.LNAL.Falsifier

open IndisputableMonolith
open IndisputableMonolith.LNAL

/‑!
# RTL Co‑Simulation (Scoped Harness)

This harness treats the reference Lean VM as a "golden" model and an RTL stub
that mirrors the VM step semantics. We record traces enriched with per-window
J‑budget counters and falsifier flags, then ensure:

1. VM and RTL traces agree tick-by-tick (sanity check for the stub).
2. Eight-tick boundaries align with `lCycle` expectations (`winIdx8 = 0`,
   `winSum8 = 0`).
3. Per-window J-budget never increases within a window and resets correctly at
   boundaries.
4. No falsifier flag trips during the scoped run.
-/

structure Trace where
  step       : Nat
  winIdx8    : Nat
  winSum8    : Int
  windowCnt  : Nat
  jBudgetWin : Nat
  jBudgetMax : Nat
  winJAccum  : Nat
  flags      : FalsifierFlags
  falsified  : Bool
  deriving Repr, DecidableEq

@[simp] def snapshot (step : Nat) (s : LState) : Trace :=
  { step := step
    , winIdx8 := s.winIdx8
    , winSum8 := s.winSum8
    , windowCnt := s.windowCount
    , jBudgetWin := s.jBudgetWin
    , jBudgetMax := s.jBudgetMax
    , winJAccum := s.winJAccum
    , flags := s.flags
    , falsified := s.falsified }

/-- RTL stub: assumed equivalent to VM (placeholder for real RTL). -/
@[simp] def rtlStep (P : LProgram) (s : LState) : LState := lStep P s

def vmTrace (P : LProgram) (s0 : LState) (n : Nat) : List Trace :=
  (List.range (n+1)).map (fun k => snapshot k (Function.iterate (lStep P) k s0))

def rtlTrace (P : LProgram) (s0 : LState) (n : Nat) : List Trace :=
  (List.range (n+1)).map (fun k => snapshot k (Function.iterate (rtlStep P) k s0))

def tracesEqual (vm rtl : List Trace) : Bool := vm = rtl

def lCycleAligned : List Trace → Bool
  | [] => true
  | ts =>
      ts.all fun t =>
        if t.step % 8 = 0 then
          decide (t.winIdx8 = 0 ∧ t.winSum8 = 0)
        else
          true

def jBudgetMonotone : List Trace → Bool
  | [] | [_] => true
  | t :: t' :: rest =>
      let ok :=
        if t'.step % 8 = 0 then
          decide (t'.jBudgetWin = t'.jBudgetMax)
        else
          decide (t'.jBudgetWin ≤ t.jBudgetWin)
      if ok then jBudgetMonotone (t' :: rest) else false

def falsifiersClear : List Trace → Bool :=
  List.all fun t => bnot t.falsified && bnot (FalsifierFlags.any t.flags)

def main : IO UInt32 := do
  -- Build a tiny program: GIVE,BALANCE,VECTOR_EQ
  let code : Array LInstr := #[
    LInstr.tokenDelta Opcode.BRAID 1,
    LInstr.balance BalanceMode.window,
    LInstr.listen ListenMode.vectorReset
  ]
  let P := mkProgram code
  let s0 := LState.init Reg6.zero Aux5.zero
  let steps := 64
  let vm := vmTrace P s0 steps
  let rtl := rtlTrace P s0 steps
  let traceOk := tracesEqual vm rtl
  let lcycleOk := lCycleAligned vm
  let jbudgetOk := jBudgetMonotone vm
  let falsifierOk := falsifiersClear vm

  if traceOk && lcycleOk && jbudgetOk && falsifierOk then
    IO.println "[RTLCoSim] Trace, lCycle, and JBudget alignment: OK" >> pure 0
  else
    do
      if ¬ traceOk then
        IO.eprintln "[RTLCoSim][FAIL] Trace mismatch between VM and RTL"
      if ¬ lcycleOk then
        IO.eprintln "[RTLCoSim][FAIL] lCycle alignment violated (winIdx8/winSum8)"
      if ¬ jbudgetOk then
        IO.eprintln "[RTLCoSim][FAIL] JBudget monotonicity violated"
      if ¬ falsifierOk then
        IO.eprintln "[RTLCoSim][FAIL] Falsifier flag triggered during run"
      pure 1
