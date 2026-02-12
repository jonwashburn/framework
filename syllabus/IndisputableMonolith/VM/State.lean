import Mathlib
import IndisputableMonolith.Config.Flags
import IndisputableMonolith.LNAL.Registers
import IndisputableMonolith.LNAL.VM

namespace IndisputableMonolith.VM

open IndisputableMonolith
open IndisputableMonolith.LNAL

private def flags : Config.Flags := Config.default

/-- Feature flag mirror for the VM module. -/
def enableV2Certs : Bool := flags.enableV2Certs

/-- VM state wrapper that tracks per-window budgeting for vNext certificates. -/
structure LState where
  /-- Base LNAL VM state (legacy semantics). -/
  base : LNAL.LState
  /-- Monotone window counter (increments every eight ticks). -/
  windowIdx : Nat
  /-- Current window J budget accumulator. -/
  winJ : Nat
  /-- Previous window J budget snapshot. -/
  winJPrev : Nat
deriving Repr

namespace LState

/-- Initialize the augmented VM state from legacy registers. -/
@[simp] def init (reg6 : Reg6) (aux5 : Aux5) : LState :=
  let base := LNAL.LState.init reg6 aux5
  { base := base, windowIdx := 0, winJ := 0, winJPrev := 0 }

/-- Detect if the current window budget has been depleted. -/
def winJZero (s : LState) : Bool := s.winJ = 0

end LState

/-- Update the J budget accumulator, rolling snapshots at window boundaries. -/
def jBudgetUpdate (s : LState) : LState :=
  let boundary := s.base.winIdx8 = 0
  let winJPrev := if boundary then s.winJ else s.winJPrev
  let winJ := if boundary then 0 else s.winJ + 1
  { s with winJ := winJ, winJPrev := winJPrev }

/-- Wrapped small-step that preserves legacy semantics while tracking vNext counters. -/
def lStep (P : LProgram) (s : LState) : LState :=
  let base' := LNAL.lStep P s.base
  let boundary := base'.winIdx8 = 0
  let windowIdx := if boundary then s.windowIdx + 1 else s.windowIdx
  let s' := { s with base := base', windowIdx := windowIdx }
  if enableV2Certs then
    jBudgetUpdate s'
  else
    { s' with winJ := s.winJ, winJPrev := s.winJPrev }

/-- Eight-tick cycle helper derived from the wrapped stepper. -/
def lCycle (P : LProgram) (s : LState) : LState :=
  Nat.iterate (lStep P) 8 s

end IndisputableMonolith.VM
