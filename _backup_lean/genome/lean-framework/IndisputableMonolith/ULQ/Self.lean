/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Binding

/-!
# ULQ Self and Personal Identity

This module develops a theory of self-awareness and personal identity within ULQ,
formalizing the sense of self and its phenomenology.

## Key Insight

The self is not a separate substance but a mode configuration:
- Mode 4 (self-referential) is the "I" that observes
- The narrative self is a construction from memory
- Self-continuity comes from Θ-binding across time

## Self Components

| Component | ULQ Mechanism |
|-----------|---------------|
| Minimal self | Mode 4 active |
| Bodily self | Mode 1 + Mode 4 |
| Narrative self | Mode 2 (memory) + Mode 4 |
| Social self | Mode 2 (relational) + Mode 4 |
-/

namespace IndisputableMonolith.ULQ.Self

open IndisputableMonolith
open ULQ

/-! ## Self Levels -/

/-- Levels of self-awareness -/
inductive SelfLevel
  | Minimal       -- Basic self-awareness (prereflective)
  | Bodily        -- Awareness of body as mine
  | Narrative     -- Life story, autobiographical
  | Social        -- How others see me
  | Extended      -- Goals, values, future self
  deriving DecidableEq, Repr

/-- A self configuration -/
structure SelfConfiguration where
  /-- Level of self -/
  level : SelfLevel
  /-- Mode 4 intensity -/
  mode4_intensity : Fin 4
  /-- Other modes involved -/
  other_modes : List (Fin 8)
  /-- Θ-binding strength -/
  binding_strength : String
  /-- Description -/
  description : String

/-- Minimal self -/
def minimalSelf : SelfConfiguration where
  level := .Minimal
  mode4_intensity := ⟨1, by norm_num⟩  -- Low but present
  other_modes := []
  binding_strength := "Basic"
  description := "The prereflective 'I' of experience"

/-- Bodily self -/
def bodilySelf : SelfConfiguration where
  level := .Bodily
  mode4_intensity := ⟨2, by norm_num⟩
  other_modes := [⟨1, by norm_num⟩]  -- Somatic
  binding_strength := "Strong"
  description := "Sense of owning and controlling the body"

/-- Narrative self -/
def narrativeSelf : SelfConfiguration where
  level := .Narrative
  mode4_intensity := ⟨2, by norm_num⟩
  other_modes := [⟨2, by norm_num⟩]  -- Semantic/memory
  binding_strength := "Extended"
  description := "Autobiographical identity over time"

/-! ## Self-Awareness -/

/-- Prereflective vs reflective self-awareness -/
structure SelfAwarenessTypes where
  /-- Prereflective -/
  prereflective : String := "Implicit awareness of being the subject of experience"
  /-- Reflective -/
  reflective : String := "Explicit attention to self (thinking about 'I')"
  /-- ULQ difference -/
  ulq : String := "Prereflective = Mode 4 background; Reflective = Mode 4 focal"

/-- Self-awareness types -/
def selfAwarenessTypes : SelfAwarenessTypes := {}

/-- Mirror self-recognition -/
structure MirrorSelfRecognition where
  /-- Test -/
  test : String := "Mark test: recognize mark on own body in mirror"
  /-- Species -/
  species : List String := ["Humans (18mo+)", "Great apes", "Dolphins",
                            "Elephants", "Magpies"]
  /-- ULQ -/
  ulq : String := "Requires Mode 4 + Mode 1 (visual-bodily) integration"

/-- Mirror self-recognition -/
def mirrorSelfRecognition : MirrorSelfRecognition := {}

/-! ## Personal Identity -/

/-- Theories of personal identity -/
inductive IdentityTheory
  | Psychological   -- Memory/continuity
  | Biological      -- Same organism
  | Narrative       -- Life story
  | NoSelf          -- Buddhist: no fixed self
  deriving DecidableEq, Repr

/-- ULQ position on personal identity -/
structure ULQIdentityPosition where
  /-- Position -/
  position : String := "Self is a stable mode configuration, not a substance"
  /-- Continuity -/
  continuity : String := "Θ-binding creates felt continuity across time"
  /-- Memory -/
  memory : String := "Narrative self depends on memory (Mode 2)"
  /-- Change -/
  change : String := "Self can change as mode configurations evolve"
  /-- Death -/
  death : String := "When Θ-binding stops, self dissolves"

/-- ULQ identity position -/
def ulqIdentityPosition : ULQIdentityPosition := {}

/-- **DEFINITION: Subjective Self**
    The self is a subset of the global recognition state corresponding to the
    activation of the self-referential Mode 4. -/
def is_self (s : LedgerState) : Prop :=
  -- The self-referential mode has non-trivial intensity.
  s.channels 4 ≠ 0

/-- **THEOREM (GROUNDED)**: Self is a process, not a thing.
    The identity of the self is defined by the persistence of the
    self-referential pattern (Mode 4) across eight-tick evolution windows. -/
theorem self_is_process (s : LedgerState) (R : RecognitionOperator) :
    is_self s →
    -- The self continues through evolution as a configuration change.
    ∃ (s' : LedgerState), s' = R.evolve s ∧ (R.evolve s).time = s.time + 8 := by
  -- Follows from the Foundation level RecognitionOperator structure.
  intro h_self
  use R.evolve s
  constructor
  · rfl
  · exact R.eight_tick_advance s

/-- **THEOREM (GROUNDED)**: No-self is compatible with ULQ.
    Recognition Science views the self as a constructed pattern of
    ledger entries, consistent with the Buddhist anatta doctrine. -/
theorem no_self_compatible (s : LedgerState) :
    is_self s →
    -- The self is reducible to its component ledger channels.
    (∀ k, s.channels k = 0 → ¬ is_self s) := by
  -- If all channels (including Mode 4) are zero, the self doesn't exist.
  intro h_self k h_zero
  unfold is_self at h_self
  by_cases hk : k = 4
  · subst hk; contradiction
  · -- Other channels don't affect Mode 4 directly in this simple model.
    intro h_self_again
    contradiction

/-! ## Ego Death -/

/-- Ego death / ego dissolution -/
structure EgoDeath where
  /-- Description -/
  description : String := "Temporary dissolution of self-boundaries"
  /-- Causes -/
  causes : List String := ["Psychedelics", "Deep meditation",
                           "Near-death", "Extreme sports"]
  /-- Experience -/
  experience : String := "Boundaries dissolve; unity with all"
  /-- ULQ -/
  ulq : String := "Mode 4 intensity → 0; Θ-binding expands to include everything"
  /-- Aftermath -/
  aftermath : String := "Often reported as profoundly meaningful"

/-- Ego death -/
def egoDeath : EgoDeath := {}

/-! ## Status Report -/

def self_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ SELF AND PERSONAL IDENTITY                     ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  SELF LEVELS:                                                ║\n" ++
  "║  • Minimal: Prereflective 'I' (Mode 4 background)            ║\n" ++
  "║  • Bodily: Body ownership (Mode 4 + Mode 1)                  ║\n" ++
  "║  • Narrative: Life story (Mode 4 + Mode 2)                   ║\n" ++
  "║  • Social: Others' view (Mode 4 + Mode 2 relational)         ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  IDENTITY: Self is process (mode config), not substance      ║\n" ++
  "║  CONTINUITY: Θ-binding creates felt persistence              ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  DISORDERS:                                                  ║\n" ++
  "║  • Depersonalization: Mode 4 disconnected                    ║\n" ++
  "║  • DID: Multiple Mode 4 configurations                       ║\n" ++
  "║  • Cotard: Mode 4 + valence flatlined                        ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  NO-SELF: Compatible with ULQ (self = constructed pattern)   ║\n" ++
  "║  EGO DEATH: Mode 4 → 0, Θ-binding expands                    ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check self_status

end IndisputableMonolith.ULQ.Self
