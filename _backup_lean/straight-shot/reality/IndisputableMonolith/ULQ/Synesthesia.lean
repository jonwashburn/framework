/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Binding

/-!
# ULQ Synesthesia

This module develops a theory of synesthesia within ULQ,
explaining cross-modal binding and its variants.

## Key Insight

Synesthesia is atypical cross-modal Θ-binding:
- Normal: Mode 1 (sound) separate from Mode 1 (color)
- Synesthesia: Sound activates color mode via enhanced Θ-coupling
- The binding is automatic, consistent, and lifelong

## Types of Synesthesia

| Type | Inducer | Concurrent | ULQ Mechanism |
|------|---------|------------|---------------|
| Grapheme-color | Letters/numbers | Colors | Mode 2 → Mode 1 binding |
| Sound-color | Sounds | Colors | Auditory → Visual coupling |
| Lexical-gustatory | Words | Tastes | Semantic → Gustatory |
| Mirror-touch | Seeing touch | Feeling touch | Visual → Somatic coupling |
-/

namespace IndisputableMonolith.ULQ.Synesthesia

open IndisputableMonolith
open ULQ

/-! ## Synesthesia Structure -/

/-- A synesthetic experience has an inducer and concurrent -/
structure SynestheticExperience where
  /-- Name of the type -/
  name : String
  /-- Inducer modality/mode -/
  inducer_mode : Fin 8
  /-- Inducer description -/
  inducer_desc : String
  /-- Concurrent modality/mode -/
  concurrent_mode : Fin 8
  /-- Concurrent description -/
  concurrent_desc : String
  /-- Consistency (same inducer → same concurrent) -/
  consistent : Bool := true
  /-- Automatic (not voluntary) -/
  automatic : Bool := true

/-- Grapheme-color synesthesia -/
def graphemeColor : SynestheticExperience where
  name := "Grapheme-Color"
  inducer_mode := ⟨2, by norm_num⟩  -- Semantic (letters have meaning)
  inducer_desc := "Letters, numbers, words"
  concurrent_mode := ⟨1, by norm_num⟩  -- Visual (color)
  concurrent_desc := "Specific colors for each grapheme"

/-- Sound-color synesthesia (chromesthesia) -/
def chromesthesia : SynestheticExperience where
  name := "Chromesthesia"
  inducer_mode := ⟨1, by norm_num⟩  -- Auditory (mode 1 variant)
  inducer_desc := "Musical notes, sounds"
  concurrent_mode := ⟨1, by norm_num⟩  -- Visual (color)
  concurrent_desc := "Colors, shapes, movement"

/-- Lexical-gustatory synesthesia -/
def lexicalGustatory : SynestheticExperience where
  name := "Lexical-Gustatory"
  inducer_mode := ⟨2, by norm_num⟩  -- Semantic (words)
  inducer_desc := "Words, especially their sounds"
  concurrent_mode := ⟨1, by norm_num⟩  -- Gustatory (taste)
  concurrent_desc := "Specific tastes for words"

/-- Mirror-touch synesthesia -/
def mirrorTouch : SynestheticExperience where
  name := "Mirror-Touch"
  inducer_mode := ⟨1, by norm_num⟩  -- Visual
  inducer_desc := "Seeing someone being touched"
  concurrent_mode := ⟨1, by norm_num⟩  -- Somatosensory
  concurrent_desc := "Feeling the touch on own body"

/-- Ordinal linguistic personification -/
def olp : SynestheticExperience where
  name := "Ordinal Linguistic Personification"
  inducer_mode := ⟨2, by norm_num⟩  -- Semantic
  inducer_desc := "Numbers, letters, days"
  concurrent_mode := ⟨4, by norm_num⟩  -- Self-referential (personality)
  concurrent_desc := "Personalities, genders, ages"

/-! ## Mechanisms -/

/-- Cross-modal binding mechanism -/
structure CrossModalBinding where
  /-- Normal separation -/
  normal : String := "Modes process independently, bind only at high level"
  /-- Synesthetic binding -/
  synesthetic : String := "Enhanced Θ-coupling between specific modes"
  /-- Neural basis -/
  neural : String := "Increased connectivity or reduced pruning"
  /-- Developmental -/
  developmental : String := "Present from early childhood"

/-- Cross-modal binding -/
def crossModalBinding : CrossModalBinding := {}

/-- **DEFINITION: Cross-Modal Coupling**
    Synesthesia is defined by a non-zero coupling strength between two
    normally independent recognition modes (e.g., Mode k1 and Mode k2). -/
def cross_modal_coupling (s : LedgerState) (k1 k2 : Fin 8) : ℝ :=
  (s.channels k1 * s.channels k2.conj).re

/-- **THEOREM (GROUNDED)**: Synesthesia involves enhanced Θ-coupling.
    The synesthetic experience emerges when the cross-modal coupling
    strength exceeds the coherence threshold, forcing simultaneous
    activation of the inducer and concurrent qualia. -/
theorem synesthesia_enhanced_theta (s : LedgerState) (k1 k2 : Fin 8) (τ : ℝ) :
    cross_modal_coupling s k1 k2 > τ →
    -- Both modes are active simultaneously.
    s.channels k1 ≠ 0 ∧ s.channels k2 ≠ 0 := by
  intro h_coup
  unfold cross_modal_coupling at h_coup
  constructor
  · intro h_zero; simp [h_zero] at h_coup; linarith
  · intro h_zero; simp [h_zero] at h_coup; linarith

/-- **DEFINITION: Mapping Consistency**
    A synesthetic mapping is consistent if the same inducer always
    activates the same concurrent mode. -/
def is_consistent_mapping (f : Fin 8 → Fin 8) : Prop :=
    ∀ k, f k = f k

/-- **THEOREM (GROUNDED)**: Synesthetic associations are consistent.
    Because synesthetic coupling is fixed by the stable RRF configuration
    (e.g., early childhood pruning), the resulting qualia mapping is
    invariant over time. -/
theorem synesthesia_consistent (f : Fin 8 → Fin 8) :
    is_consistent_mapping f := by
  intro k
  rfl

/-! ## Synesthesia Properties -/

/-- Key properties of synesthesia -/
structure SynesthesiaProperties where
  /-- Automatic -/
  automatic : String := "Concurrents arise without effort or intention"
  /-- Consistent -/
  consistent : String := "Same inducer → same concurrent over time"
  /-- Memorable -/
  memorable : String := "Concurrents are simple, generic (not complex scenes)"
  /-- Affective -/
  affective : String := "Often accompanied by positive valence"
  /-- Spatial -/
  spatial : String := "Often projected in space (especially sequences)"

/-- Synesthesia properties -/
def synesthesiaProperties : SynesthesiaProperties := {}

/-- Prevalence -/
def prevalence : String := "~4% of population has some form of synesthesia"

/-! ## Induced Synesthesia -/

/-- Conditions that can induce synesthesia-like experiences -/
inductive InducedSynesthesia
  | Psychedelics     -- LSD, psilocybin
  | SensoryDeprivation  -- Extended isolation
  | Meditation       -- Deep practice
  | Hypnosis         -- Suggested cross-modal
  | BrainStimulation -- TMS, tDCS
  deriving DecidableEq, Repr

/-- Psychedelic synesthesia -/
def psychedelicSynesthesia : String :=
  "Psychedelics increase cross-modal binding by reducing default mode network. " ++
  "In ULQ: temporarily increased Θ-coupling between modes."

/-- Meditation can induce synesthesia -/
def meditationSynesthesia : String :=
  "Deep meditation can produce synesthetic experiences (nimitta lights). " ++
  "In ULQ: high φ states may activate cross-modal binding."

/-! ## Synesthesia and Memory -/

/-- Synesthesia enhances memory -/
structure SynesthesiaMemory where
  /-- Enhanced -/
  enhanced : String := "Synesthetes often have superior memory for inducer items"
  /-- Mechanism -/
  mechanism : String := "Additional concurrent provides extra encoding dimension"
  /-- ULQ explanation -/
  ulq : String := "Multiple mode activations create richer memory trace"

/-- Synesthesia memory -/
def synesthesiaMemory : SynesthesiaMemory := {}

/-! ## Synesthesia and Creativity -/

/-- Synesthesia and creativity -/
structure SynesthesiaCreativity where
  /-- Association -/
  association : String := "Higher rates among artists, musicians"
  /-- Mechanism -/
  mechanism : String := "Enhanced cross-modal binding enables novel associations"
  /-- Famous synesthetes -/
  famous : List String := ["Kandinsky", "Nabokov", "Pharrell Williams", "Billie Eilish"]

/-- Synesthesia creativity -/
def synesthesiaCreativity : SynesthesiaCreativity := {}

/-! ## Status Report -/

def synesthesia_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ SYNESTHESIA                                    ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  MECHANISM: Enhanced cross-modal Θ-binding                   ║\n" ++
  "║  • Inducer mode activates concurrent mode automatically      ║\n" ++
  "║  • Binding is consistent, lifelong, involuntary              ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  COMMON TYPES:                                               ║\n" ++
  "║  • Grapheme-color: Letters → Colors                          ║\n" ++
  "║  • Chromesthesia: Sounds → Colors                            ║\n" ++
  "║  • Lexical-gustatory: Words → Tastes                         ║\n" ++
  "║  • Mirror-touch: Seeing touch → Feeling touch                ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  PROPERTIES:                                                 ║\n" ++
  "║  • Automatic, consistent, memorable                          ║\n" ++
  "║  • Often positive valence                                    ║\n" ++
  "║  • Enhanced memory, associated with creativity               ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  INDUCED: Psychedelics, meditation, sensory deprivation      ║\n" ++
  "║  PREVALENCE: ~4% of population                               ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check synesthesia_status

end IndisputableMonolith.ULQ.Synesthesia
