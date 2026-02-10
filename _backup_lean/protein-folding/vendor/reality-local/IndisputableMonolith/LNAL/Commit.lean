import Mathlib
import IndisputableMonolith.LNAL.VM
import IndisputableMonolith.LNAL.JBudget

namespace IndisputableMonolith
namespace LNAL

/-- A COMMIT boundary event emitted when crossing an 8‑tick window boundary. -/
structure CommitEvent where
  /-- Global step index where the boundary was reached. -/
  stepIndex : Nat
  /-- Window index after the step (always 0 at boundary). -/
  winIdx    : Nat
deriving Repr, DecidableEq

/-- Detect a commit event for a single step transition. -/
def detectCommit (s s' : LState) (t : Nat) : Option CommitEvent :=
  if s.winIdx8 = 7 ∧ s'.winIdx8 = 0 then
    some { stepIndex := t + 1, winIdx := s'.winIdx8 }
  else none

/-- Run `n` steps and collect commit events along the trace. -/
def runWithCommits (P : LProgram) (s0 : LState) (n : Nat) : List CommitEvent :=
  let rec loop (t : Nat) (s : LState) (acc : List CommitEvent) : List CommitEvent :=
    if h : t < n then
      let s' := lStep P s
      let acc' := match detectCommit s s' t with
                  | some e => e :: acc
                  | none   => acc
      loop (t+1) s' acc'
    else acc.reverse
  loop 0 s0 []

/-- Static commit window (index and ΔJ cost). -/
structure CommitWindow where
  window : Nat
  deltaJ : Nat
deriving Repr, DecidableEq

/-- Compute commit windows from compiled code using ΔJ bars. -/
def commitWindowsFromCode (code : Array LInstr) (threshold : Nat := 1) : List CommitWindow :=
  let djList := (deltaJPerWindow code).toList
  (List.zip (List.range djList.length) djList).foldl (fun acc (idx, dj) =>
    if dj ≥ threshold then acc.concat { window := idx, deltaJ := dj }
    else acc) []

/-- Extract runtime COMMIT events from an `LState`. -/
def runtimeCommitWindows (s : LState) : List CommitWindow :=
  s.commitHistory.map (fun entry => { window := entry.fst, deltaJ := entry.snd })

/-- Latest COMMIT event emitted during the last step, if available. -/
def commitPendingWindow (s : LState) : Option CommitWindow := do
  let win ← s.commitPending
  match s.commitHistory.find? (fun entry => entry.fst = win) with
  | some entry => pure { window := win, deltaJ := entry.snd }
  | none => none

end LNAL
end IndisputableMonolith
