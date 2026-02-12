import Mathlib
import Lean.Data.Json
import IndisputableMonolith.LNAL.Registers
import IndisputableMonolith.LNAL.Opcodes
import IndisputableMonolith.LNAL.InstrCost
import IndisputableMonolith.LNAL.Falsifier

namespace IndisputableMonolith
namespace LNAL

@[simp] def breathPeriod : Nat := 1024
-- Legacy generic VM removed: the typed LNAL VM appears below.

end LNAL
end IndisputableMonolith

--------------------------------------------------------------------------------
-- LNAL-specific execution (typed registers + LNAL opcodes)
--------------------------------------------------------------------------------

namespace IndisputableMonolith
namespace LNAL

abbrev LProgram := Nat → LInstr

structure LState where
  reg6   : Reg6
  aux5   : Aux5
  ip     : Nat
  breath : Nat
  halted : Bool
  winSum8 : Int
  winIdx8 : Nat
  flipped : Bool
  vecSumCycle : Int
  /-- Per-window J budget (monotone nonincreasing across a window). -/
  jBudgetWin : Nat
  /-- Configured per-window budget allowance (reset target when the window rolls). -/
  jBudgetMax : Nat := 4
  /-- Historical record of closing budgets for completed windows (most recent last). -/
  jBudgetHistory : List Nat := []
  /-- Count of completed 8-op windows. -/
  windowCount : Nat := 0
  /-- Accumulated positive J-cost within the current window. -/
  winJAccum : Nat := 0
  /-- Threshold (ΔJ) for emitting COMMIT events. -/
  commitThreshold : Nat := 1
  /-- History of COMMIT events as (window index, ΔJ). -/
  commitHistory : List (Nat × Nat) := []
  /-- Most recent COMMIT event emitted by the last step, if any. -/
  commitPending : Option Nat := none
  /-- Whether the ConsentDerivative gate is enabled for runtime checks. -/
  consentGate : Bool := false
  /-- Runtime falsifier flags (sticky). -/
  flags : FalsifierFlags := {}
  /-- Sticky falsified bit: once true, remains true. -/
  falsified : Bool := false
deriving Repr

namespace LState

@[simp] def init (reg6 : Reg6) (aux5 : Aux5) : LState :=
  { reg6 := reg6, aux5 := aux5, ip := 0, breath := 0, halted := false,
    winSum8 := 0, winIdx8 := 0, flipped := false, vecSumCycle := 0,
    jBudgetWin := 4, jBudgetMax := 4, jBudgetHistory := [],
    windowCount := 0, winJAccum := 0, commitThreshold := 1,
    commitHistory := [], commitPending := none,
    consentGate := false, flags := {}, falsified := false }

@[simp] def enableConsentGate (s : LState) : LState :=
  { s with consentGate := true }

end LState

@[simp] def lFetch (P : LProgram) (ip : Nat) : LInstr := P ip
@[simp] def lNextIP (s : LState) : Nat := s.ip + 1
@[simp] def lBumpBreath (s : LState) : Nat := (s.breath + 1) % breathPeriod

@[simp] def clamp01 (x : Int) : Int := if x ≤ 0 then 0 else if 1 ≤ x then 1 else x

@[simp] def clampI32 (x : Int) : Int :=
  if x ≤ (-i32Bound) then (-i32Bound + 1)
  else if i32Bound ≤ x then (i32Bound - 1)
  else x

@[simp] def applyTokenAction (a5 : Aux5) (act : TokenAction) : Aux5 × Int :=
  match act with
  | TokenAction.delta d =>
      let newTok := clamp01 (a5.tokenCt + d)
      ({ a5 with tokenCt := newTok }, d)
  | TokenAction.set value _ =>
      let newTok := clamp01 value
      ({ a5 with tokenCt := newTok }, 0)

@[simp] def foldDirFromArg (arg : OpcodeArg) : Int :=
  match arg with
  | OpcodeArg.fold dir => if dir = 0 then 1 else dir
  | _ => 1

def lStep (P : LProgram) (s : LState) : LState :=
  let core :=
    if s.halted then s else
      let i := lFetch P s.ip
      -- advance window index
      let advIdx : Nat := (s.winIdx8 + 1) % 8
      let cycAdd : Int := s.vecSumCycle + s.reg6.kPerp
      let costVal : Int := instrCost i
      -- JBudget update: consume budget on positive-cost ops (Int.toNat saturates negatives)
      let budgetDec : Nat := Int.toNat costVal
      let budget' : Nat := s.jBudgetWin - budgetDec
      let unitsLeakAttempt : Bool := budgetDec > s.jBudgetWin
      let windowAccum : Nat := if s.winIdx8 = 0 then budgetDec else s.winJAccum + budgetDec
      let s' : LState :=
        match i.op with
        | Opcode.LOCK =>
            { s with aux5 := { s.aux5 with phaseLock := true }, winIdx8 := advIdx, vecSumCycle := cycAdd, jBudgetWin := budget' }
        | Opcode.FLIP =>
            let mid : Nat := breathPeriod / 2 - 1
            let flipped' := if s.breath = mid then not s.flipped else s.flipped
            { s with flipped := flipped', winIdx8 := advIdx, vecSumCycle := cycAdd, jBudgetWin := budget' }
        | Opcode.BALANCE =>
            let (winSum', winIdx') :=
              match i.arg with
              | OpcodeArg.balance BalanceMode.cycle =>
                  if s.breath = breathPeriod - 1 then (0, 0) else (s.winSum8, advIdx)
              | _ =>
                  let ws := if s.winIdx8 = 7 then 0 else s.winSum8
                  (ws, advIdx)
            { s with winSum8 := winSum', winIdx8 := winIdx', vecSumCycle := cycAdd, jBudgetWin := budget' }
        | Opcode.FOLD =>
            let dir := foldDirFromArg i.arg
            let r6 := s.reg6
            let r6' := { r6 with nuPhi := clampI32 (r6.nuPhi + dir) }
            { s with reg6 := r6', winIdx8 := advIdx, vecSumCycle := cycAdd, jBudgetWin := budget' }
        | Opcode.SEED =>
            let (aux', _) :=
              match i.arg with
              | OpcodeArg.token act => applyTokenAction s.aux5 act
              | _ => applyTokenAction s.aux5 (TokenAction.set 1)
            { s with aux5 := aux', winIdx8 := advIdx, vecSumCycle := cycAdd, jBudgetWin := budget' }
        | Opcode.BRAID =>
            let (aux', winDelta) :=
              match i.arg with
              | OpcodeArg.token act => applyTokenAction s.aux5 act
              | _ => (s.aux5, 0)
            { s with aux5 := aux', winSum8 := s.winSum8 + winDelta, winIdx8 := advIdx, vecSumCycle := cycAdd, jBudgetWin := budget' }
        | Opcode.MERGE =>
            let (aux', winDelta) :=
              match i.arg with
              | OpcodeArg.token act => applyTokenAction s.aux5 act
              | _ => (s.aux5, 0)
            { s with aux5 := aux', winSum8 := s.winSum8 + winDelta, winIdx8 := advIdx, vecSumCycle := cycAdd, jBudgetWin := budget' }
        | Opcode.LISTEN =>
            let vecSum' :=
              match i.arg with
              | OpcodeArg.listen ListenMode.vectorReset => if s.breath = breathPeriod - 1 then 0 else cycAdd
              | _ => cycAdd
            { s with winIdx8 := advIdx, vecSumCycle := vecSum', jBudgetWin := budget' }
      let s'' := { s' with ip := lNextIP s', winJAccum := windowAccum, commitPending := none }
      let rollover : Bool := advIdx = 0
      let windowCloseBudget := s''.jBudgetWin
      let history' := if rollover then s''.jBudgetHistory.concat windowCloseBudget else s''.jBudgetHistory
      let budgetNext := if rollover then s''.jBudgetMax else s''.jBudgetWin
      let (commitHist', windowCount', winJAccumNext, commitPending') :=
        if rollover then
          let windowIdx := s.windowCount
          let commitFire := windowAccum ≥ s.commitThreshold
          let hist := if commitFire then s.commitHistory ++ [(windowIdx, windowAccum)] else s.commitHistory
          let nextPending := if commitFire then some windowIdx else none
          (hist, s.windowCount + 1, 0, nextPending)
        else
          (s.commitHistory, s.windowCount, windowAccum, none)
      let sFinal := { s'' with
        jBudgetWin := budgetNext,
        jBudgetHistory := history',
        commitHistory := commitHist',
        windowCount := windowCount',
        winJAccum := winJAccumNext,
        commitPending := commitPending' }
      -- Falsifier updates at boundary/step
      let nonNeutral := rollover ∧ (sFinal.winSum8 ≠ (0 : Int))
      let jUp := costVal < 0
      let consentFail :=
        if s.consentGate then
          match i.op, i.arg with
          | Opcode.BRAID, OpcodeArg.token (TokenAction.delta d)
          | Opcode.MERGE, OpcodeArg.token (TokenAction.delta d) => d < 0
          | Opcode.SEED, OpcodeArg.token (TokenAction.set _ cost) => cost < 0
          | _, _ => false
        else false
      let flags' : FalsifierFlags := {
        nonNeutralWindow := s.flags.nonNeutralWindow ∨ nonNeutral,
        jIncreased := s.flags.jIncreased ∨ jUp,
        unitsLeak := s.flags.unitsLeak ∨ unitsLeakAttempt,
        consentViolation := s.flags.consentViolation ∨ consentFail }
      let falsified' := s.falsified ∨ FalsifierFlags.any flags'
      { sFinal with flags := flags', falsified := falsified' }
  { core with breath := lBumpBreath core }

lemma l_breath_lt_period (P : LProgram) (s : LState) : (lStep P s).breath < breathPeriod := by
  dsimp [lStep, lBumpBreath, breathPeriod]
  by_cases hH : s.halted
  ·
    have hpos : 0 < breathPeriod := by decide
    simpa [hH] using Nat.mod_lt (s.breath + 1) hpos
  ·
    have hpos : 0 < breathPeriod := by decide
    exact Nat.mod_lt _ hpos

--------------------------------------------------------------------------------
-- Small‑step semantics (relational form)
--------------------------------------------------------------------------------

/-- One small‑step of the LNAL VM (relational form). -/
inductive LStepRel (P : LProgram) : LState → LState → Prop where
  | step (s : LState) : LStepRel P s (lStep P s)

/-- Determinism: the step relation produces a unique successor. -/
theorem LStepRel.deterministic {P : LProgram} {s s₁ s₂ : LState}
    (h₁ : LStepRel P s s₁) (h₂ : LStepRel P s s₂) : s₁ = s₂ := by
  cases h₁ <;> cases h₂ <;> rfl

/-- Reflexive–transitive closure of small‑steps. -/
abbrev LStar (P : LProgram) := Relation.ReflTransGen (LStepRel P)

/-- Functional step embeds into the relational step. -/
@[simp] theorem lStep_as_rel (P : LProgram) (s : LState) :
    LStepRel P s (lStep P s) := LStepRel.step s

/-- Simple well‑formedness predicate: breath is always within the period. -/
def BreathBound (s : LState) : Prop := s.breath < breathPeriod

/-- Progress: every state can take a small‑step (possibly self if halted). -/
theorem progress (P : LProgram) (s : LState) : ∃ s', LStepRel P s s' := by
  exact ⟨lStep P s, lStep_as_rel P s⟩

/-- Preservation (breath bound): stepping keeps breath within period. -/
theorem preservation_breath (P : LProgram) (s : LState) :
    BreathBound (lStep P s) := by
  -- direct from arithmetic lemma
  simpa [BreathBound] using l_breath_lt_period P s

--------------------------------------------------------------------------------
-- Hardware test vectors and invariants
--------------------------------------------------------------------------------

namespace Hardware

open Classical
open Lean

/-- Convert an instruction array into a total LNAL program. -/
@[simp] def programOfArray (code : Array LInstr) : LProgram :=
  fun idx =>
    if h : idx < code.size then
      code[idx]
    else
      LInstr.simple Opcode.LOCK

private def traceAux (program : LProgram) : Nat → LState → List LState
  | 0, s => [s]
  | Nat.succ n, s =>
      let next := lStep program s
      s :: traceAux program n next

/-- Simulate `steps` successive VM transitions starting from the default initial state. -/
@[simp] def simulateTrace (code : Array LInstr) (steps : Nat)
    (reg6 : Reg6 := Reg6.zero) (aux5 : Aux5 := Aux5.zero) : List LState :=
  let program := programOfArray code
  let init := LState.init reg6 aux5
  traceAux program steps init

/-- Baseline register configuration for hardware vectors (unit-balanced, k⊥ = 1). -/
@[simp] def testReg6 : Reg6 := { Reg6.zero with kPerp := 1, tau := 1, ell := 1 }

/-- Baseline auxiliary register configuration for hardware vectors. -/
@[simp] def testAux5 : Aux5 := Aux5.zero

/-- Eight-op program exercising K-gate token flow and window neutrality. -/
@[simp] def kGateProgram : Array LInstr := #[
  LInstr.tokenSet Opcode.SEED 1,
  LInstr.tokenDelta Opcode.BRAID 1,
  LInstr.tokenDelta Opcode.MERGE (-1),
  LInstr.fold 1,
  LInstr.fold (-1),
  LInstr.listen ListenMode.noop,
  LInstr.simple Opcode.FLIP,
  LInstr.balance BalanceMode.window
]

/-- Sixteen-op program covering two full eight-beat windows. -/
@[simp] def eightBeatProgram : Array LInstr :=
  kGateProgram ++ kGateProgram

/-- Trace covering one K-gate program execution. Includes the initial state. -/
def kGateTrace : List LState :=
  simulateTrace kGateProgram kGateProgram.size testReg6 testAux5

/-- Trace covering two successive eight-beat windows. -/
def eightBeatTrace : List LState :=
  simulateTrace eightBeatProgram eightBeatProgram.size testReg6 testAux5

/-- Consecutive state pairs extracted from a trace. -/
private def consecutivePairs {α} : List α → List (α × α)
  | [] => []
  | [_] => []
  | x :: y :: rest => (x, y) :: consecutivePairs (y :: rest)

/-- Last state of a nonempty trace, if present. -/
private def lastState? : List LState → Option LState
  | [] => none
  | [s] => some s
  | _ :: rest => lastState? rest

/-- Enumerated K-gate vector exposing window index, vector sum, and window sum. -/
def kGateVector : List (Nat × Nat × Int × Int) :=
  (List.zip (List.range kGateTrace.length) kGateTrace).map fun
    | (step, st) => (step, st.winIdx8, st.vecSumCycle, st.winSum8)

/-- Enumerated eight-beat vector exposing window/count progression and commit flag. -/
def eightBeatVector : List (Nat × Nat × Nat × Bool) :=
  (List.zip (List.range eightBeatTrace.length) eightBeatTrace).map fun
    | (step, st) => (step, st.winIdx8, st.windowCount, st.commitPending.isSome)

/-- Hardware invariant: vector sum increments exactly by k⊥ each step. -/
def kGateIncrementInvariant : Bool :=
  (consecutivePairs kGateTrace).all fun
    | (s, s') =>
        if s'.vecSumCycle = s.vecSumCycle + s.reg6.kPerp then
          true
        else
          false

/-- Hardware invariant: eight-beat windows stay within index bounds and reset neutrally. -/
def eightBeatAlignmentInvariant : Bool :=
  let idxOk := eightBeatTrace.all fun s => decide (s.winIdx8 < 8)
  let resetOk := eightBeatTrace.all fun s =>
    if s.winIdx8 = 0 then decide (s.winSum8 = 0) else true
  let expectedWindows := (eightBeatProgram.size + 7) / 8
  let windowOk :=
    match lastState? eightBeatTrace with
    | some final => decide (final.windowCount = expectedWindows)
    | none => false
  idxOk && resetOk && windowOk

/-- Detail string summarising the terminal K-gate state. -/
def kGateIncrementDetail : String :=
  match lastState? kGateTrace with
  | some final =>
      s!"vec_sum_cycle={final.vecSumCycle}, k_perp={final.reg6.kPerp}"
  | none => "no-trace"

/-- Detail string summarising the terminal eight-beat state. -/
def eightBeatAlignmentDetail : String :=
  let expected := (eightBeatProgram.size + 7) / 8
  match lastState? eightBeatTrace with
  | some final =>
      s!"window_count={final.windowCount} (expected {expected}), win_sum8={final.winSum8}"
  | none => "no-trace"

@[simp] def jsonOfNat (n : Nat) : Json := Json.str (toString n)
@[simp] def jsonOfInt (z : Int) : Json := Json.str (toString z)

private def statusJson (name : String) (ok : Bool) (detail : String) : Json :=
  Json.mkObj [
    ("name", Json.str name),
    ("passed", Json.bool ok),
    ("detail", Json.str detail)
  ]

/-- JSON-encoded K-gate test vector for hardware validation. -/
def kGateVectorJson : Json :=
  let payload := kGateVector.map fun
    | (step, idx, vec, win) =>
        Json.mkObj [
          ("step", jsonOfNat step),
          ("win_idx8", jsonOfNat idx),
          ("vec_sum_cycle", jsonOfInt vec),
          ("win_sum8", jsonOfInt win)
        ]
  Json.arr (Array.mk payload)

/-- JSON-encoded eight-beat test vector for hardware validation. -/
def eightBeatVectorJson : Json :=
  let payload := eightBeatVector.map fun
    | (step, idx, windows, commit) =>
        Json.mkObj [
          ("step", jsonOfNat step),
          ("win_idx8", jsonOfNat idx),
          ("window_count", jsonOfNat windows),
          ("commit_pending", Json.bool commit)
        ]
  Json.arr (Array.mk payload)

/-- Combined JSON payload containing vectors and invariant pass/fail flags. -/
def hardwareInvariantsJson : Json :=
  let invariantPayload : List Json := [
    statusJson "k_gate_increment" kGateIncrementInvariant kGateIncrementDetail,
    statusJson "eight_beat_alignment" eightBeatAlignmentInvariant eightBeatAlignmentDetail
  ]
  Json.mkObj [
    ("vectors", Json.mkObj [
      ("k_gate", kGateVectorJson),
      ("eight_beat", eightBeatVectorJson)
    ]),
    ("invariants", Json.arr (Array.mk invariantPayload))
  ]

/-- JSON string exposing the K-gate hardware test vector. -/
def k_gate_vector_json : String := toString kGateVectorJson

/-- JSON string exposing the eight-beat hardware test vector. -/
def eight_beat_vector_json : String := toString eightBeatVectorJson

/-- JSON summary of hardware invariants and associated test vectors. -/
def hardware_invariants_json : String := toString hardwareInvariantsJson

end Hardware

-- #eval IndisputableMonolith.LNAL.Hardware.k_gate_vector_json
-- #eval IndisputableMonolith.LNAL.Hardware.eight_beat_vector_json
-- #eval IndisputableMonolith.LNAL.Hardware.hardware_invariants_json

end LNAL
end IndisputableMonolith
