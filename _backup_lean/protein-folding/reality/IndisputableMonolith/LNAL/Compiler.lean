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
  commitWindows : List Commit.CommitWindow := []
  jGreedy       : List Schedule.JGreedyWindow := []
  progressWitnesses : List ProgressWitness := []
deriving Repr

private def windowSlice (code : Array LInstr) (w : Nat) : Array LInstr :=
  let start := 8 * w
  let stop := Nat.min code.size (start + 8)
  code.extract start stop

private def progressWitnesses (code : Array LInstr) (deltaJ : Array Nat)
    (packets : PhiIR.PacketAnalysis) : List ProgressWitness :=
  let windowCount := deltaJ.size
  (List.range windowCount).map fun w =>
    let windowInstrs := windowSlice code w
    let hasCost := windowInstrs.any (fun instr => JBudget.posCost instr > 0)
    let delta := deltaJ.getD w 0
    let status := if delta > 0 ∨ hasCost then ProgressStatus.progress else ProgressStatus.stuck
    let packetInfo := packets.packets.find?
      (fun pkt => pkt.window = w)
    let neutralDesc : String :=
      match packetInfo with
      | some pkt => s!"neutral={pkt.neutral}; netΔ={pkt.netDelta}"
      | none => "neutrality=unknown"
    let reason :=
      if status = ProgressStatus.progress then
        s!"ΔJ={delta}"
      else
        let base := "No positive-cost ops in window"
        match packetInfo with
        | some pkt => s!"{base} ({neutralDesc}; balances={pkt.balanceCount})"
        | none => base
    { window := w, deltaJ := delta, status := status, reason := reason }

private def hasBalanceEvery8 (code : Array LInstr) : Bool :=
  let n := code.size
  if n < 8 then true else Id.run do
    for i in [0:n] do
      if i + 8 ≤ n then
        let mut seen := false
        for j in [i:i+8] do
          if (code.get! j).op = Opcode.BALANCE then
            seen := true
        if ¬ seen then return false
    return true

private def hasVectorEqEvery1024 (code : Array LInstr) : Bool :=
  let n := code.size
  if n < 1024 then true else Id.run do
    for i in [0:n] do
      if i + 1024 ≤ n then
        let mut seen := false
        for j in [i:i+1024] do
          let instr := code.get! j
          match instr.op, instr.arg with
          | Opcode.LISTEN, OpcodeArg.listen ListenMode.vectorReset =>
              seen := true
          | _, _ => ()
        if ¬ seen then return false
    return true

private def noListenDoubleStall (code : Array LInstr) : Bool :=
  let n := code.size
  if n = 0 then true else Id.run do
    for i in [0:n-1] do
      let a := code.get! i
      let b := code.get! (i+1)
      if a.op = Opcode.LISTEN ∧ b.op = Opcode.LISTEN then
        return false
    return true

private def tokenParityAndCostOk (code : Array LInstr) : Bool × Bool :=
  -- Simulate a single-voxel token counter and a cost accumulator
  let n := code.size
  let mut t : Int := 0
  let mut c : Int := 0
  let mut parityOk := true
  let mut costOk := true
  for i in [0:n] do
    let instr := code.get! i
    match instr.op, instr.arg with
    | Opcode.SEED, OpcodeArg.token (TokenAction.set value cost) =>
        t := value
        c := c + cost
    | Opcode.BRAID, OpcodeArg.token (TokenAction.delta d) =>
        t := t + d
        c := c + d
    | Opcode.MERGE, OpcodeArg.token (TokenAction.delta d) =>
        t := t + d
        c := c + d
    | _, _ => ()
    if t < 0 ∨ 1 < t then parityOk := false
    if c < -4 ∨ 4 < c then costOk := false
  (parityOk, costOk)

private def gcSeedWithinWindow (code : Array LInstr) (window : Nat := 24) : Bool :=
  let n := code.size
  Id.run do
    for i in [0:n] do
      let instr := code.get! i
      if instr.op = Opcode.SEED then
        let hi := Nat.min n (i + window + 1)
        let mut seen := false
        for j in [i+1:hi] do
          match (code.get! j).op, (code.get! j).arg with
          | Opcode.SEED, OpcodeArg.token (TokenAction.set 0 _) => seen := true
          | _, _ => ()
        if ¬ seen then return false
    return true

private def hasAtLeastOneFlip (code : Array LInstr) : Bool :=
  code.any (fun i => i.op = Opcode.FLIP)

private def consentViolationIndices (code : Array LInstr) : List Nat :=
  code.toList.enum.foldl (fun acc (idx, instr) =>
    match instr.op, instr.arg with
    | Opcode.BRAID, OpcodeArg.token (TokenAction.delta d)
    | Opcode.MERGE, OpcodeArg.token (TokenAction.delta d) =>
        if d < 0 then acc.concat idx else acc
    | Opcode.SEED, OpcodeArg.token (TokenAction.set _ cost) =>
        if cost < 0 then acc.concat idx else acc
    | _, _ => acc) []

def staticChecks (code : Array LInstr) (phi : PhiIR.PhiAnalysis := {
    literals := #[]
    errors := #[]
    duplicateNames := []
  }) (packets : PhiIR.PacketAnalysis := {}) (consentEnabled : Bool := false) : CompileReport :=
  let w8 := hasBalanceEvery8 code
  let v1024 := hasVectorEqEvery1024 code
  let lst := noListenDoubleStall code
  let (tokOk, costOk) := tokenParityAndCostOk code
  let gcOk := gcSeedWithinWindow code 24
  let flipAny := hasAtLeastOneFlip code
  let jMono := Certificates.JMonotoneCert.fromProgram code
  let consentViol := consentViolationIndices code
  let mut errs : List String := []
  let mut warns : List String := []
  if ¬ w8 then errs := errs.concat "Missing BALANCE in at least one 8-instruction window"
  if ¬ v1024 then errs := errs.concat "Missing VECTOR_EQ (LISTEN reset) in at least one 1024-instruction window"
  if ¬ lst then errs := errs.concat "LISTEN appears in consecutive steps (double-stall forbidden)"
  if ¬ tokOk then errs := errs.concat "Token parity violated (tokenCt must remain in {0,1})"
  if ¬ costOk then errs := errs.concat "Cost ceiling exceeded (|net token delta| must remain ≤ 4)"
  if ¬ gcOk then errs := errs.concat "SEED must be followed by GC_SEED within ≤ 3 cycles (approx. 24 steps)"
  if ¬ flipAny then errs := errs.concat "At least one FLIP opcode must appear per breath schedule"
  if ¬ jMono.ok then errs := errs ++ jMono.errors
  let budgetCap : Nat := 4
  let overBudgetWindows : List Nat :=
    (jMono.deltaJ.toList.enum.filter (fun (_, v) => v > budgetCap)).map (·.fst)
  if ¬ overBudgetWindows.isEmpty then
    let windowStr := String.intercalate ", " (overBudgetWindows.map (fun n => ToString.toString n))
    errs := errs.concat s!"Window ΔJ exceeds JBudget({budgetCap}) in windows {windowStr}"
  let phiErrors := phi.errors.toList.map (fun (info : Nat × String) =>
    let (line, msg) := info
    s!"@phi line {line + 1}: {msg}")
  if ¬ phiErrors.isEmpty then
    errs := errs ++ phiErrors
  if ¬ phi.duplicateNames.isEmpty then
    warns := warns ++ phi.duplicateNames.map (fun name =>
      s!"Duplicate @phi label '{name}'")
  if ¬ packets.errors.isEmpty then
    errs := errs ++ packets.errors
  let consentIdxStr := String.intercalate ", " (consentViol.map (fun n => ToString.toString n))
  if consentEnabled ∧ ¬ consentViol.isEmpty then
    errs := errs.concat s!"ConsentDerivative gate violated at steps {consentIdxStr}"
  if ¬ consentEnabled ∧ ¬ consentViol.isEmpty then
    warns := warns.concat s!"ConsentDerivative gate would flag steps {consentIdxStr}"
  let consentReport : ConsentReport := {
    enabled := consentEnabled,
    ok := if consentEnabled then consentViol.isEmpty else true,
    violations := consentViol
  }
  let commits := Commit.commitWindowsFromCode code
  let greedy := Schedule.jGreedySchedule code
  let progress := progressWitnesses code jMono.deltaJ packets
  let stuckWitnesses := progress.filter (fun w => w.status = ProgressStatus.stuck)
  if ¬ stuckWitnesses.isEmpty then
    warns := warns ++ stuckWitnesses.map
      (fun witness => s!"Window {witness.window}: {witness.reason}")
  { ok := errs.isEmpty,
    errors := errs,
    warnings := warns,
    jMonotone := jMono,
    phiAnalysis := phi,
    phiPackets := packets,
    consent := consentReport,
    commitWindows := commits,
    jGreedy := greedy,
    progressWitnesses := progress }

def compile (src : String) (consentEnabled : Bool := false) : CompileReport × Except ParseError LProgram :=
  match parseProgramFull src with
  | .error e => ({ ok := false, errors := [s!"Parse error: {e}"] }, .error e)
  | .ok out =>
    let rep := staticChecks out.code out.phi out.packets consentEnabled
    if rep.ok then (rep, .ok (mkProgram out.code)) else (rep, .ok (mkProgram out.code))

end LNAL
end IndisputableMonolith
