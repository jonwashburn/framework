import Mathlib
import Lean.Data.Json
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.VM
import IndisputableMonolith.LNAL.Invariants

/-!
# LNAL Hardware Pathway: Test Vectors and Invariants JSON

Generate simple VM test vectors that exercise the eight‑beat alignment window
and expose hardware‑level invariants as JSON suitable for Verilog testbenches.

We include a placeholder K‑gate check boolean for integration, and a concrete
eight‑beat neutrality check derived from the VM semantics.
-/

namespace IndisputableMonolith
namespace LNAL

open Lean

/-- A minimal eight‑beat program: `BALANCE` at idx=7, `LOCK` elsewhere. -/
def simpleEightBeatProgram : LProgram := fun ip =>
  if ip % 8 = 7 then LInstr.balance BalanceMode.window else LInstr.simple Opcode.LOCK

/-- Run `n` steps from an initial state and collect the states. -/
def traceStates (P : LProgram) (s0 : LState) (n : Nat) : List LState :=
  List.range (n + 1) |>.map (fun k => Function.iterate (lStep P) k s0)

/-- Check neutrality every 8th step up to horizon `n`. -/
def eightBeatNeutralUpTo (P : LProgram) (s0 : LState) (n : Nat) : Bool :=
  let kMax := n / 8
  let ok (k : Nat) :=
    let s := Function.iterate (lStep P) (8 * k) s0
    (s.winIdx8 = 0) ∧ (s.winSum8 = 0)
  (List.range (kMax + 1)).all (fun k => decide (ok k))

/-- Placeholder K‑gate equality check (integration hook). -/
def kGateEqualityOK : Bool := true

private def jsonOfInt (x : Int) : Json := Json.str (toString x)

/-- Produce a compact JSON summary of hardware invariants over a short trace. -/
def hardware_invariants_json (steps : Nat := 32) : String :=
  let P := simpleEightBeatProgram
  let s0 := LState.init default default
  let states := traceStates P s0 steps
  let idxTrace := Json.arr <| Array.mk (states.map (fun s => Json.num s.winIdx8))
  let breathTrace := Json.arr <| Array.mk (states.map (fun s => Json.num s.breath))
  let sumTrace := Json.arr <| Array.mk (states.map (fun s => jsonOfInt s.winSum8))
  let eightOk := eightBeatNeutralUpTo P s0 steps
  let obj := Json.mkObj [
    ("steps", Json.num steps),
    ("k_gate_ok", Json.bool kGateEqualityOK),
    ("eight_beat_ok", Json.bool eightOk),
    ("trace", Json.mkObj [
      ("winIdx8", idxTrace),
      ("breath", breathTrace),
      ("winSum8", sumTrace)
    ])
  ]
  toString obj

/-- Demo: JSON report for hardware invariants. -/
#eval hardware_invariants_json 64

end LNAL
end IndisputableMonolith
