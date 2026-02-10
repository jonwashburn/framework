import Mathlib
import IndisputableMonolith.LNAL.Parser
import IndisputableMonolith.Certificates.JMonotone
import IndisputableMonolith.LNAL.Commit
import IndisputableMonolith.LNAL.JBudget
import IndisputableMonolith.LNAL.Schedule

namespace IndisputableMonolith
namespace LNAL

structure ConsentReport where
  enabled    : Bool := false
  ok         : Bool := true
  violations : List Nat := []
deriving Repr

inductive ProgressStatus
| progress
| stuck
deriving DecidableEq, Repr

structure ProgressWitness where
  window : Nat
  deltaJ : Nat
  status : ProgressStatus
  reason : String
deriving Repr

structure CompileReport where
  ok           : Bool
  errors       : List String := []
  warnings     : List String := []
  jMonotone    : Certificates.JMonotoneCert := { ok := true }
  phiAnalysis  : PhiIR.PhiAnalysis := {
    literals := #[]
    errors := #[]
    duplicateNames := []
  }
  phiPackets  : PhiIR.PacketAnalysis := {}
  consent      : ConsentReport := {}
  commitWindows : List CommitWindow := []
  jGreedy       : List JGreedyWindow := []
  progressWitnesses : List ProgressWitness := []
deriving Repr

/-- Simplified static checks (stubbed for build) -/
def staticChecks (code : Array LInstr) (phi : PhiIR.PhiAnalysis := {
    literals := #[]
    errors := #[]
    duplicateNames := []
  }) (packets : PhiIR.PacketAnalysis := {}) (consentEnabled : Bool := false) : CompileReport :=
  { ok := true,
    errors := [],
    warnings := [],
    jMonotone := Certificates.JMonotoneCert.fromProgram code,
    phiAnalysis := phi,
    phiPackets := packets,
    consent := { enabled := consentEnabled, ok := true, violations := [] },
    commitWindows := commitWindowsFromCode code,
    jGreedy := jGreedySchedule code,
    progressWitnesses := [] }

def compile (src : String) (consentEnabled : Bool := false) : CompileReport × Except ParseError LProgram :=
  match parseProgramFull src with
  | .error e => ({ ok := false, errors := ["Parse error"], commitWindows := [], jGreedy := [] }, .error e)
  | .ok out =>
    let rep := staticChecks out.code out.phi out.packets consentEnabled
    if rep.ok then (rep, .ok (mkProgram out.code)) else (rep, .ok (mkProgram out.code))

end LNAL
end IndisputableMonolith
