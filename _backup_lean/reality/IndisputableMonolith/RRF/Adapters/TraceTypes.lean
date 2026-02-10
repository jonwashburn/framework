import Mathlib.Data.List.Basic

/-!
# RRF Adapters: Trace Types

Lean structures for RSFold/CPM traces at the level we want to reason about.

This module defines the types that connect Lean formalization to empirical artifacts.
The actual audit logic is in separate modules.

## Trace Schema

A CPM trace consists of:
- Sequence of moves (accepted or rejected)
- Energy values at each step
- Phase information (LOCK/BALANCE)
- Optional: sonification events
-/


namespace IndisputableMonolith
namespace RRF.Adapters

/-! ## Basic Trace Types -/

/-- A residue index in a protein. -/
abbrev ResidueIndex := Nat

/-- A 3D coordinate. -/
structure Point3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- A single CPM move. -/
structure CPMMove where
  /-- Which residue was moved. -/
  residue : ResidueIndex
  /-- Old position (CA atom). -/
  oldPos : Point3
  /-- New position (CA atom). -/
  newPos : Point3
  /-- Was the move accepted? -/
  accepted : Bool
  /-- Energy before move. -/
  energyBefore : Float
  /-- Energy after move. -/
  energyAfter : Float
  deriving Repr

/-- CPM optimization phase. -/
inductive CPMPhase where
  | heat : CPMPhase
  | lock : CPMPhase
  | balance : CPMPhase
  deriving DecidableEq, Repr, Inhabited

/-- A CPM trace: a sequence of moves with metadata. -/
structure CPMTrace where
  /-- The sequence. -/
  sequence : String
  /-- All moves attempted. -/
  moves : List CPMMove
  /-- Phase at each iteration. -/
  phases : List CPMPhase
  /-- Temperature at each iteration. -/
  temperatures : List Float
  /-- Final RMSD (if reference available). -/
  finalRMSD : Option Float
  deriving Repr

/-! ## Trace Invariants -/

/-- Energy should generally decrease (except for thermal fluctuations). -/
def energyDecreasingTrend (trace : CPMTrace) : Bool :=
  let accepted := trace.moves.filter (·.accepted)
  let energies := accepted.map (·.energyAfter)
  match energies with
  | [] => true
  | e₀ :: rest =>
    let final := rest.getLast?.getD e₀
    final ≤ e₀

/-- Acceptance rate in a phase. -/
def acceptanceRateInPhase (trace : CPMTrace) (phase : CPMPhase) : Float :=
  let inPhase := trace.moves.zip trace.phases
    |>.filter (fun (_, p) => p == phase)
    |>.map (·.1)
  if inPhase.isEmpty then 0.0
  else
    let accepted := inPhase.filter (·.accepted) |>.length
    Float.ofNat accepted / Float.ofNat inPhase.length

/-- Balance phase should have lower acceptance rate than Lock. -/
def balanceHasLowerAcceptance (trace : CPMTrace) : Bool :=
  acceptanceRateInPhase trace .lock > acceptanceRateInPhase trace .balance

/-! ## Sonification Events -/

/-- A sonification event from folding. -/
structure SonificationEvent where
  /-- Tick number. -/
  tick : Nat
  /-- Residue involved. -/
  residue : ResidueIndex
  /-- WToken index (0-19). -/
  wtoken : Fin 20
  /-- Strain at this event. -/
  strain : Float
  /-- Detune in cents (from pitch bend). -/
  detuneCents : Float
  deriving Repr

/-- A sonification trace. -/
structure SonificationTrace where
  events : List SonificationEvent
  deriving Repr

/-- Mean absolute detune (the consonance metric). -/
def meanAbsoluteDetune (trace : SonificationTrace) : Float :=
  if trace.events.isEmpty then 0.0
  else
    let total := trace.events.foldl (fun acc e => acc + Float.abs e.detuneCents) 0.0
    total / Float.ofNat trace.events.length

/-! ## LNAL Trace Types -/

/-- LNAL opcode. -/
inductive LNALOp where
  | nop : LNALOp
  | push : Int → LNALOp
  | pop : LNALOp
  | add : LNALOp
  | mul : LNALOp
  | dup : LNALOp
  | swap : LNALOp
  | flip : LNALOp
  | lock : LNALOp
  | balance : LNALOp
  deriving DecidableEq, Repr

/-- LNAL execution step. -/
structure LNALStep where
  /-- Tick number. -/
  tick : Nat
  /-- Phase (0-7). -/
  phase : Fin 8
  /-- Opcode executed. -/
  op : LNALOp
  /-- Register state after. -/
  registers : List Int
  /-- J-cost after. -/
  jcost : Float
  deriving Repr

/-- LNAL execution trace. -/
structure LNALTrace where
  steps : List LNALStep
  deriving Repr

/-- Check if trace respects 8-tick cycle. -/
def respectsEightTick (trace : LNALTrace) : Bool :=
  trace.steps.all (fun step => step.tick % 8 == step.phase.val)

end RRF.Adapters
end IndisputableMonolith
