/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.AlteredStates

/-!
# ULQ Dream Phenomenology

This module develops a theory of dream experience within ULQ,
formalizing dream states, lucid dreaming, and dream content.

## Key Insight

Dreams represent a lowered C-threshold state where:
- Mode combinations occur that wouldn't survive waking scrutiny
- Binding (Θ-coupling) is weakened, allowing discontinuities
- Valence is often intensified (nightmares, euphoric dreams)

## Dream Characteristics

| Feature | ULQ Explanation |
|---------|-----------------|
| Bizarreness | Weakened mode coherence constraints |
| Emotional intensity | Reduced frontal valence modulation |
| Discontinuity | Reduced Θ-binding across time |
| Acceptance | Lower C-threshold doesn't reject |
| Forgetting | Weak memory encoding (low φ) |
-/

namespace IndisputableMonolith.ULQ.Dreams

open IndisputableMonolith
open ULQ

/-! ## Dream States -/

/-- A dream state has modified ULQ parameters -/
structure DreamState where
  /-- C threshold is reduced -/
  c_threshold : ℕ := 0  -- Below normal 1
  /-- Mode coherence is relaxed -/
  mode_coherence : String := "Reduced"
  /-- Θ-binding is weakened -/
  theta_binding : String := "Weakened"
  /-- Valence modulation is reduced -/
  valence_modulation : String := "Reduced frontal control"
  /-- Memory encoding is weak -/
  memory_encoding : String := "Weak hippocampal binding"

/-- Normal dream state -/
def normalDream : DreamState := {}

/-- REM sleep parameters -/
structure REMState where
  /-- High cortical activation -/
  cortical_activation : String := "High (similar to waking)"
  /-- Muscle atonia -/
  muscle_atonia : String := "Complete (prevents acting out)"
  /-- Theta rhythm -/
  theta_rhythm : String := "Prominent hippocampal theta"
  /-- Dream report likelihood -/
  dream_report : String := "80% if awakened"

/-- REM sleep -/
def remSleep : REMState := {}

/-! ## Dream Content -/

/-- Types of dream content -/
inductive DreamContent
  | Mundane        -- Everyday scenarios
  | Bizarre        -- Impossible combinations
  | Emotional      -- Intense feelings
  | Lucid          -- Aware of dreaming
  | Recurring      -- Repeated themes
  | Prophetic      -- Future-seeming
  | Nightmarish    -- Intensely negative
  deriving DecidableEq, Repr

/-- Dream content signature -/
structure DreamContentSignature where
  /-- Content type -/
  content : DreamContent
  /-- Mode pattern -/
  mode_pattern : String
  /-- Intensity level -/
  intensity : String
  /-- Valence -/
  valence : String

/-- Nightmare signature -/
def nightmareSignature : DreamContentSignature where
  content := .Nightmarish
  mode_pattern := "Threat modes (3,5,7) dominant"
  intensity := "High (φ-level 2-3)"
  valence := "Strongly negative"

/-- Euphoric dream signature -/
def euphoricDreamSignature : DreamContentSignature where
  content := .Emotional
  mode_pattern := "Reward modes (1,2) dominant"
  intensity := "High"
  valence := "Strongly positive"

/-! ## Lucid Dreaming -/

/-- Lucid dream state -/
structure LucidDreamState where
  /-- Base dream state -/
  base : DreamState
  /-- Metacognitive awareness -/
  metacognition : String := "Active ('I know I'm dreaming')"
  /-- Frontal activation -/
  frontal : String := "Partially restored"
  /-- Control level -/
  control : String := "Variable (0-100%)"
  /-- Stability -/
  stability : String := "Fragile (easily lost)"

/-- Lucid dream -/
def lucidDream : LucidDreamState where
  base := normalDream

/-- **DEFINITION: Lucidity Awareness**
    A dream state is lucid if it includes active metacognitive monitoring
    (Mode 4) of the internal generated content. -/
def is_lucid (s : LedgerState) : Prop :=
  s.channels 4 ≠ 0 ∧ ∃ k, k ≠ 4 ∧ s.channels k ≠ 0

/-- **HYPOTHESIS**: Dream binding stability is lower than waking stability, requiring partial C-restoration for lucidity.
    STATUS: EMPIRICAL_HYPO
    TEST_PROTOCOL: Comparison of C-level proxies (e.g., complexity measures) in lucid vs non-lucid REM sleep.
    FALSIFIER: Occurrence of lucid dreaming in states with zero recognition cost (C=0). -/
def H_DreamBinding : Prop :=
  ∀ (s : LedgerState), is_lucid s → Foundation.RecognitionCost s ≥ 1

/-- **THEOREM (GROUNDED)**: Lucidity requires partial C restoration.
    The meta-cognitive awareness of dreaming (lucidity) is only possible
    when the local recognition cost $C$ is sufficient to support
    simultaneous activation of the self-referential and content modes. -/
theorem lucidity_needs_c (h : H_DreamBinding) (s : LedgerState) :
    is_lucid s →
    -- Lucidity implies the state has crossed the minimal consciousness threshold.
    Foundation.RecognitionCost s ≥ 1 := by
  intro hl
  exact h s hl

/-- Techniques for inducing lucidity -/
inductive LucidityTechnique
  | RealityTesting   -- Habitual checks
  | MILD             -- Mnemonic Induction
  | WILD             -- Wake Initiated
  | WBTB             -- Wake Back To Bed
  | SSILD            -- Senses Initiated
  deriving DecidableEq, Repr

/-- Reality testing works by strengthening metacognitive mode -/
def realityTestingMechanism : String :=
  "Habitual reality checks strengthen mode 4 (self-referential), " ++
  "increasing chance of mode 4 activation in dreams"

/-! ## Dream Interpretation -/

/-- Dream elements and their qualia signatures -/
structure DreamElement where
  /-- Element type -/
  element : String
  /-- Typical mode -/
  mode : Fin 8
  /-- Typical valence -/
  valence : String
  /-- Interpretation -/
  interpretation : String

/-- Flying dreams -/
def flyingDream : DreamElement where
  element := "Flying"
  mode := ⟨3, by norm_num⟩  -- Dynamic/kinesthetic
  valence := "Usually positive (freedom)"
  interpretation := "Mode 3 activation without gravity constraints"

/-- Falling dreams -/
def fallingDream : DreamElement where
  element := "Falling"
  mode := ⟨3, by norm_num⟩  -- Dynamic/kinesthetic
  valence := "Usually negative (fear)"
  interpretation := "Threat-activated mode 3"

/-- Teeth falling out -/
def teethDream : DreamElement where
  element := "Teeth falling out"
  mode := ⟨1, by norm_num⟩  -- Body image
  valence := "Negative (loss, vulnerability)"
  interpretation := "Body schema mode with loss valence"

/-- Being chased -/
def chasedDream : DreamElement where
  element := "Being chased"
  mode := ⟨3, by norm_num⟩  -- Dynamic + threat
  valence := "Strongly negative"
  interpretation := "Activated threat response in dynamic mode"

/-! ## Sleep Stages -/

/-- Sleep stage qualia -/
inductive SleepStage
  | Wake          -- Full consciousness
  | N1            -- Light sleep, hypnagogia
  | N2            -- Deeper, sleep spindles
  | N3            -- Slow wave, deep
  | REM           -- Dreaming
  deriving DecidableEq, Repr

/-- Hypnagogia (N1 entry) -/
structure Hypnagogia where
  /-- Description -/
  description : String := "Transitional state between wake and sleep"
  /-- Hallucinations -/
  hallucinations : String := "Visual, auditory snippets"
  /-- C level -/
  c_level : String := "Fluctuating around 1"
  /-- Mode state -/
  mode_state : String := "Fragmented, rapidly shifting"

/-- Hypnagogia -/
def hypnagogia : Hypnagogia := {}

/-- Hypnopompia (waking from sleep) -/
structure Hypnopompia where
  /-- Description -/
  description : String := "Transitional state between sleep and wake"
  /-- Sleep paralysis risk -/
  paralysis : String := "Possible (REM atonia persisting)"
  /-- Dream intrusion -/
  intrusion : String := "Dream imagery may persist"

/-- Hypnopompia -/
def hypnopompia : Hypnopompia := {}

/-! ## Dream Functions -/

/-- Proposed functions of dreaming -/
inductive DreamFunction
  | MemoryConsolidation    -- Strengthening memories
  | EmotionalProcessing    -- Processing emotions
  | ThreatSimulation       -- Practicing responses
  | CreativeProblemSolving -- Novel combinations
  | WasteRemoval           -- Glymphatic clearance
  deriving DecidableEq, Repr

/-- Memory consolidation during dreams -/
def memoryConsolidation : String :=
  "Dreams replay experiences, strengthening synaptic connections. " ++
  "In ULQ: rehearsal of mode-valence associations."

/-- Threat simulation theory -/
def threatSimulation : String :=
  "Dreams disproportionately feature threats (being chased, falling). " ++
  "In ULQ: practicing threat-mode responses in safe environment."

/-! ## Status Report -/

def dreams_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ DREAM PHENOMENOLOGY                            ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  DREAM STATE:                                                ║\n" ++
  "║  • C threshold: Reduced (below 1)                            ║\n" ++
  "║  • Mode coherence: Relaxed (bizarre combinations)            ║\n" ++
  "║  • Θ-binding: Weakened (discontinuities accepted)            ║\n" ++
  "║  • Valence: Intensified (reduced frontal modulation)         ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  LUCID DREAMING:                                             ║\n" ++
  "║  • Metacognition: 'I know I'm dreaming'                      ║\n" ++
  "║  • Mechanism: Partial frontal/C restoration                  ║\n" ++
  "║  • Techniques: Reality testing, MILD, WILD, WBTB             ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  COMMON DREAMS:                                              ║\n" ++
  "║  • Flying: Mode 3, positive valence (freedom)                ║\n" ++
  "║  • Falling: Mode 3, negative valence (fear)                  ║\n" ++
  "║  • Chased: Mode 3 + threat, strongly negative                ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check dreams_status

end IndisputableMonolith.ULQ.Dreams
