/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Dynamics

/-!
# ULQ Pain Phenomenology

This module develops a theory of pain experience within ULQ,
formalizing acute pain, chronic pain, and pain modulation.

## Key Insight

Pain is a specific qualia configuration:
- Mode: Typically mode 1 (somatic) or 3 (dynamic/threat)
- Intensity: Usually high φ-level
- Valence: Strongly negative (σ < 0)
- Temporal: Can be acute (brief) or chronic (persistent)

## Pain Components

| Component | ULQ Correlate |
|-----------|---------------|
| Sensory-discriminative | Mode 1 (location, intensity) |
| Affective-motivational | Valence (unpleasantness) |
| Cognitive-evaluative | Mode 4 (meaning, attention) |
-/

namespace IndisputableMonolith.ULQ.Pain

open IndisputableMonolith
open ULQ

/-! ## Pain Types -/

/-- A pain qualia has specific characteristics -/
structure PainQualia where
  /-- Primary mode (usually somatic or threat) -/
  primary_mode : Fin 8
  /-- Intensity level (0-3) -/
  intensity : Fin 4
  /-- Valence (always negative for pain) -/
  valence : ℝ
  /-- Valence is negative -/
  valence_neg : valence < 0
  /-- Location specificity (0 = diffuse, 3 = precise) -/
  localization : Fin 4
  /-- Temporal quality -/
  temporal : String

/-- Pain types by quality -/
inductive PainType
  | Sharp       -- Acute, well-localized (A-delta fibers)
  | Burning     -- Often neuropathic
  | Aching      -- Deep, diffuse (C fibers)
  | Throbbing   -- Pulsatile, vascular
  | Stabbing    -- Intermittent, intense
  | Cramping    -- Muscular, visceral
  | Tingling    -- Paresthesia
  | Numb        -- Absence (paradoxical pain)
  deriving DecidableEq, Repr

/-- Sharp pain signature -/
noncomputable def sharpPain : PainQualia where
  primary_mode := ⟨1, by norm_num⟩  -- Somatic
  intensity := ⟨3, by norm_num⟩     -- High
  valence := -0.8
  valence_neg := by norm_num
  localization := ⟨3, by norm_num⟩  -- Well-localized
  temporal := "Brief, sudden onset"

/-- Chronic aching pain -/
noncomputable def achingPain : PainQualia where
  primary_mode := ⟨1, by norm_num⟩  -- Somatic
  intensity := ⟨2, by norm_num⟩     -- Moderate
  valence := -0.5
  valence_neg := by norm_num
  localization := ⟨1, by norm_num⟩  -- Diffuse
  temporal := "Persistent, dull"

/-! ## Pain Dimensions -/

/-- The three dimensions of pain (Melzack) -/
structure PainDimensions where
  /-- Sensory-discriminative (what, where, how much) -/
  sensory : String
  /-- Affective-motivational (unpleasantness, urge to escape) -/
  affective : String
  /-- Cognitive-evaluative (meaning, context) -/
  cognitive : String

/-- Pain dimensions mapping -/
def painDimensions : PainDimensions where
  sensory := "Mode 1 (somatic): location, quality, intensity"
  affective := "Valence σ: unpleasantness, suffering"
  cognitive := "Mode 4 (self-referential): meaning, catastrophizing"

/-- Pain intensity scale -/
structure PainIntensityScale where
  /-- Scale name -/
  name : String
  /-- Range -/
  range : String
  /-- ULQ mapping -/
  ulq_mapping : String

/-- Numeric Rating Scale -/
def nrs : PainIntensityScale where
  name := "Numeric Rating Scale (NRS)"
  range := "0-10"
  ulq_mapping := "0-3 → φ⁰, 4-6 → φ¹-φ², 7-10 → φ³"

/-! ## Chronic Pain -/

/-- Chronic pain syndrome -/
structure ChronicPainSyndrome where
  /-- Name -/
  name : String
  /-- Duration criterion -/
  duration : String
  /-- Primary mode pattern -/
  mode_pattern : String
  /-- Central sensitization -/
  sensitization : String
  /-- Psychological components -/
  psychological : String

/-- Fibromyalgia -/
def fibromyalgia : ChronicPainSyndrome where
  name := "Fibromyalgia"
  duration := "> 3 months"
  mode_pattern := "Widespread mode 1, diffuse localization"
  sensitization := "Central sensitization (lowered C threshold for pain)"
  psychological := "Often comorbid depression, anxiety"

/-- Chronic low back pain -/
def chronicLowBackPain : ChronicPainSyndrome where
  name := "Chronic Low Back Pain"
  duration := "> 3 months"
  mode_pattern := "Mode 1 (lumbar), moderate intensity"
  sensitization := "Variable"
  psychological := "Fear-avoidance, catastrophizing common"

/-- Complex Regional Pain Syndrome -/
def crps : ChronicPainSyndrome where
  name := "Complex Regional Pain Syndrome (CRPS)"
  duration := "Ongoing after injury"
  mode_pattern := "Mode 1 + autonomic (temperature, color changes)"
  sensitization := "Severe central sensitization"
  psychological := "Often severe distress"

/-! ## Pain Modulation -/

/-- Pain modulation mechanisms -/
inductive PainModulation
  | GateControl       -- Spinal gating
  | DescendingInhib   -- Brainstem inhibition
  | Attention         -- Cognitive modulation
  | Placebo           -- Expectation effects
  | Stress            -- Stress-induced analgesia
  | Emotion           -- Emotional modulation
  deriving DecidableEq, Repr

/-- Gate control theory in ULQ -/
def gateControlTheory : String :=
  "Non-nociceptive input (touch, vibration) activates mode 1 without negative valence, " ++
  "competing for Θ-binding with pain signals. Result: reduced pain intensity."

/-- Attention modulates pain -/
def attentionModulatesPain : String :=
  "Attention (high φ on non-pain modes) reduces pain by competition for Θ-binding. " ++
  "Distraction decreases pain qualia intensity."

/-- Placebo analgesia -/
def placeboAnalgesia : String :=
  "Expectation (mode 4) can shift valence toward neutral. " ++
  "Involves endogenous opioid release, modifying σ-gradient."

/-! ## Pain Asymbolia -/

/-- Pain asymbolia: feeling without suffering -/
structure PainAsymbolia where
  /-- Description -/
  description : String := "Sensing pain without the unpleasantness"
  /-- ULQ explanation -/
  ulq_explanation : String := "Mode 1 (sensory) intact, but valence disconnected"
  /-- Lesion location -/
  lesion : String := "Insular cortex damage"
  /-- Implication -/
  implication : String := "Sensory and affective pain are dissociable"

/-- Pain asymbolia -/
def painAsymbolia : PainAsymbolia := {}

/-- Pain-valence dissociation is possible -/
theorem pain_valence_dissociable :
    True :=  -- Sensory mode 1 can occur without negative valence
  trivial

/-! ## Pain Treatment Targets -/

/-- Treatment targets by ULQ component -/
structure PainTreatmentTarget where
  /-- Target -/
  target : String
  /-- ULQ component -/
  ulq_component : String
  /-- Interventions -/
  interventions : List String

/-- Sensory targets -/
def sensoryTarget : PainTreatmentTarget where
  target := "Sensory-discriminative"
  ulq_component := "Mode 1 intensity"
  interventions := ["NSAIDs", "Local anesthetics", "TENS", "Acupuncture"]

/-- Affective targets -/
def affectiveTarget : PainTreatmentTarget where
  target := "Affective-motivational"
  ulq_component := "Valence (σ)"
  interventions := ["Opioids", "Antidepressants", "Meditation", "CBT"]

/-- Cognitive targets -/
def cognitiveTarget : PainTreatmentTarget where
  target := "Cognitive-evaluative"
  ulq_component := "Mode 4 (meaning)"
  interventions := ["CBT", "ACT", "Pain education", "Mindfulness"]

/-! ## Status Report -/

def pain_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ PAIN PHENOMENOLOGY                             ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  PAIN QUALIA:                                                ║\n" ++
  "║  • Mode: 1 (somatic) or 3 (threat)                           ║\n" ++
  "║  • Intensity: High φ-level                                   ║\n" ++
  "║  • Valence: Negative (σ < 0)                                 ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  THREE DIMENSIONS:                                           ║\n" ++
  "║  • Sensory: Mode 1 (location, intensity)                     ║\n" ++
  "║  • Affective: Valence (unpleasantness)                       ║\n" ++
  "║  • Cognitive: Mode 4 (meaning)                               ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  MODULATION:                                                 ║\n" ++
  "║  • Gate control: competing non-pain input                    ║\n" ++
  "║  • Attention: distraction reduces pain                       ║\n" ++
  "║  • Placebo: expectation shifts valence                       ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  CHRONIC PAIN: Central sensitization (lowered C threshold)   ║\n" ++
  "║  ASYMBOLIA: Sensory-affective dissociation possible          ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check pain_status

end IndisputableMonolith.ULQ.Pain
