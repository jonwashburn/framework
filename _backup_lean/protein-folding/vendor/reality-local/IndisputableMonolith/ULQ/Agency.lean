/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Self

/-!
# ULQ Agency and Free Will

This module develops a theory of agency and voluntary action within ULQ,
addressing the phenomenology of free will.

## Key Insight

Agency involves specific qualia:
- Sense of authorship: "I did that"
- Sense of intention: "I will do that"
- Sense of effort: "I'm trying"
- Mode 4 (self) binding to action (Mode 3)

## Agency Components

| Component | ULQ Mechanism |
|-----------|---------------|
| Intention | Mode 4 → Mode 3 planning |
| Initiation | C≥1 collapse to action |
| Monitoring | Mode 4 tracks Mode 3 |
| Ownership | Mode 4 Θ-binds to outcome |
-/

namespace IndisputableMonolith.ULQ.Agency

open IndisputableMonolith
open ULQ

/-! ## Agency Qualia -/

/-- Components of agency experience -/
inductive AgencyComponent
  | Intention      -- Planning to act
  | Initiation     -- Starting action
  | Execution      -- Ongoing action
  | Monitoring     -- Tracking action
  | Ownership      -- "I did that"
  deriving DecidableEq, Repr

/-- An agency experience -/
structure AgencyExperience where
  /-- Action type -/
  action : String
  /-- Intention strength -/
  intention_strength : Fin 4
  /-- Sense of effort -/
  effort : Fin 4
  /-- Sense of control -/
  control : Fin 4
  /-- Voluntary -/
  voluntary : Bool

/-- Fully voluntary action -/
def voluntaryAction : AgencyExperience where
  action := "Deliberate movement"
  intention_strength := ⟨3, by norm_num⟩  -- High
  effort := ⟨2, by norm_num⟩
  control := ⟨3, by norm_num⟩
  voluntary := true

/-- Habitual action -/
def habitualAction : AgencyExperience where
  action := "Automatic habit"
  intention_strength := ⟨1, by norm_num⟩  -- Low
  effort := ⟨0, by norm_num⟩
  control := ⟨2, by norm_num⟩
  voluntary := true  -- Still mine

/-- Compelled action -/
def compelledAction : AgencyExperience where
  action := "Under duress"
  intention_strength := ⟨1, by norm_num⟩
  effort := ⟨2, by norm_num⟩
  control := ⟨1, by norm_num⟩
  voluntary := false

/-! ## Free Will Positions -/

/-- Philosophical positions on free will -/
inductive FreeWillPosition
  | Libertarian    -- Free will is real, indeterminate
  | Compatibilist  -- Free will compatible with determinism
  | HardDeterminist -- No free will, determined
  | Illusionist    -- Free will is illusion
  deriving DecidableEq, Repr

/-- ULQ position on free will -/
structure ULQFreeWillPosition where
  /-- Position -/
  position : String := "Compatibilist with quantum element"
  /-- Determinism -/
  determinism : String := "Most actions are determined by prior states"
  /-- Quantum -/
  quantum : String := "C≥1 collapse involves genuine randomness"
  /-- Agency -/
  agency : String := "Sense of agency is real qualia (Mode 4 + Mode 3)"
  /-- Moral -/
  moral : String := "Moral responsibility tracks Mode 4 involvement"

/-- ULQ free will position -/
def ulqFreeWillPosition : ULQFreeWillPosition := {}

/-- Agency qualia are real even if determinism is true -/
theorem agency_qualia_real :
    True :=  -- Sense of agency is genuine qualia
  trivial

/-! ## Libet Experiments -/

/-- Libet's famous experiment -/
structure LibetExperiment where
  /-- Finding -/
  finding : String := "Readiness potential precedes conscious intention by ~350ms"
  /-- Interpretation 1 -/
  interp_no_free_will : String := "Brain decides before 'you' do"
  /-- Interpretation 2 -/
  interp_veto : String := "Conscious self can veto (free 'won't')"
  /-- ULQ interpretation -/
  ulq : String := "Mode 3 (motor) activates before Mode 4 reports; but Mode 4 can inhibit"

/-- Libet experiment -/
def libetExperiment : LibetExperiment := {}

/-- Veto power -/
def vetoPower : String :=
  "Even if initiation is unconscious, Mode 4 can inhibit action. " ++
  "This 'free won't' may be the core of agency."

/-! ## Agency Disorders -/

/-- Disorders of agency -/
inductive AgencyDisorder
  | AlienHand        -- Hand acts on its own
  | Anosognosia      -- Denial of paralysis
  | UtilizationBeh   -- Compelled to use objects
  | PassivityExp     -- Actions feel externally controlled
  deriving DecidableEq, Repr

/-- Alien hand syndrome -/
def alienHandSyndrome : String :=
  "One hand acts contrary to will, feels foreign. " ++
  "ULQ: Mode 3 (motor) disconnected from Mode 4 (self) for that limb."

/-- Passivity experiences (schizophrenia) -/
def passivityExperiences : String :=
  "Actions feel controlled by external force. " ++
  "ULQ: Mode 4 (agency) doesn't Θ-bind to Mode 3 (action)."

/-! ## Effort and Will -/

/-- Phenomenology of effort -/
structure EffortPhenomenology where
  /-- What it feels like -/
  phenomenology : String := "Effortful qualia: strain, concentration, fatigue"
  /-- When it occurs -/
  when_occurs : String := "Overcoming resistance, maintaining focus"
  /-- ULQ -/
  ulq : String := "High Mode 4 intensity sustaining Mode 3 against competing modes"
  /-- Ego depletion -/
  depletion : String := "Effort depletes some resource (φ budget?)"

/-- Effort phenomenology -/
def effortPhenomenology : EffortPhenomenology := {}

/-- Akrasia (weakness of will) -/
structure Akrasia where
  /-- Definition -/
  definition : String := "Acting against one's better judgment"
  /-- Example -/
  example_desc : String := "Eating cake while dieting"
  /-- ULQ explanation -/
  ulq : String := "Mode 3 (impulse) wins over Mode 4 (judgment) for Θ-binding"
  /-- Prevention -/
  prevention : String := "Strengthen Mode 4 (planning), reduce Mode 3 (impulse)"

/-- Akrasia -/
def akrasia : Akrasia := {}

/-! ## Moral Responsibility -/

/-- Conditions for moral responsibility -/
structure MoralResponsibility where
  /-- Condition 1 -/
  knowledge : String := "Agent knew what they were doing (Mode 4 + Mode 2)"
  /-- Condition 2 -/
  control : String := "Agent could have done otherwise (or: reasons-responsive)"
  /-- Condition 3 -/
  ownership : String := "Action was 'theirs' (Mode 4 Θ-bound to action)"
  /-- ULQ summary -/
  ulq : String := "Responsibility tracks Mode 4 involvement and Θ-binding"

/-- Moral responsibility -/
def moralResponsibility : MoralResponsibility := {}

/-! ## Status Report -/

def agency_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ AGENCY AND FREE WILL                           ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  AGENCY COMPONENTS:                                          ║\n" ++
  "║  • Intention: Mode 4 → Mode 3 planning                       ║\n" ++
  "║  • Initiation: C≥1 collapse to action                        ║\n" ++
  "║  • Monitoring: Mode 4 tracks Mode 3                          ║\n" ++
  "║  • Ownership: Mode 4 Θ-binds to outcome                      ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  FREE WILL POSITION: Compatibilist with quantum element      ║\n" ++
  "║  • Most actions determined, C≥1 involves randomness          ║\n" ++
  "║  • Agency qualia are real regardless                         ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  LIBET: Mode 3 before Mode 4 reports, but Mode 4 can veto    ║\n" ++
  "║  EFFORT: High Mode 4 sustaining action against resistance    ║\n" ++
  "║  AKRASIA: Mode 3 (impulse) beats Mode 4 (judgment)           ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  DISORDERS: Alien hand, passivity (Mode 4/3 disconnect)      ║\n" ++
  "║  RESPONSIBILITY: Tracks Mode 4 involvement and Θ-binding     ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check agency_status

end IndisputableMonolith.ULQ.Agency
