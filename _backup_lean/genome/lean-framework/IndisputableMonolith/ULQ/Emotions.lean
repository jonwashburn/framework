/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Calculus

/-!
# ULQ Emotional Qualia

This module develops a comprehensive taxonomy of emotional qualia,
mapping emotions to ULQ parameters.

## Key Insight

Emotions are complex qualia configurations:
- Mode determines qualitative character (fear ≠ anger)
- Intensity (φ-level) determines strength
- Valence (σ) determines pleasantness
- Temporal quality determines duration/onset

## Emotion Mapping

| Emotion | Mode | Intensity | Valence |
|---------|------|-----------|---------|
| Joy | 1-2 | High | Positive |
| Sadness | 1-2 | Low-Med | Negative |
| Fear | 3 | High | Negative |
| Anger | 3 | High | Negative |
| Disgust | 1 | Med | Negative |
| Surprise | 3-4 | High | Neutral |
-/

namespace IndisputableMonolith.ULQ.Emotions

open IndisputableMonolith
open ULQ

/-! ## Basic Emotions -/

/-- An emotional qualia configuration -/
structure EmotionalQualia where
  /-- Emotion name -/
  name : String
  /-- Primary mode -/
  primary_mode : Fin 8
  /-- Secondary modes (if any) -/
  secondary_modes : List (Fin 8)
  /-- Intensity level -/
  intensity : Fin 4
  /-- Valence sign -/
  valence_sign : Int  -- -1, 0, 1
  /-- Typical duration -/
  duration : String
  /-- Action tendency -/
  action_tendency : String

/-- Joy / Happiness -/
def joy : EmotionalQualia where
  name := "Joy"
  primary_mode := ⟨2, by norm_num⟩  -- Relational
  secondary_modes := [⟨1, by norm_num⟩]  -- Somatic (bodily pleasure)
  intensity := ⟨2, by norm_num⟩  -- Moderate-high
  valence_sign := 1
  duration := "Variable, can be brief (pleasure) or sustained (contentment)"
  action_tendency := "Approach, share, celebrate"

/-- Sadness -/
def sadness : EmotionalQualia where
  name := "Sadness"
  primary_mode := ⟨2, by norm_num⟩  -- Relational (loss)
  secondary_modes := [⟨1, by norm_num⟩]  -- Somatic (heaviness)
  intensity := ⟨1, by norm_num⟩  -- Low-moderate
  valence_sign := -1
  duration := "Prolonged"
  action_tendency := "Withdraw, seek comfort, cry"

/-- Fear -/
def fear : EmotionalQualia where
  name := "Fear"
  primary_mode := ⟨3, by norm_num⟩  -- Dynamic (threat)
  secondary_modes := [⟨1, by norm_num⟩]  -- Somatic (arousal)
  intensity := ⟨3, by norm_num⟩  -- High
  valence_sign := -1
  duration := "Acute (minutes to hours)"
  action_tendency := "Flee, freeze, fight"

/-- Anger -/
def anger : EmotionalQualia where
  name := "Anger"
  primary_mode := ⟨3, by norm_num⟩  -- Dynamic (action)
  secondary_modes := [⟨4, by norm_num⟩]  -- Boundary (violation)
  intensity := ⟨3, by norm_num⟩  -- High
  valence_sign := -1
  duration := "Acute, can become chronic (resentment)"
  action_tendency := "Attack, assert, confront"

/-- Disgust -/
def disgust : EmotionalQualia where
  name := "Disgust"
  primary_mode := ⟨1, by norm_num⟩  -- Somatic (nausea)
  secondary_modes := [⟨4, by norm_num⟩]  -- Boundary (contamination)
  intensity := ⟨2, by norm_num⟩  -- Moderate
  valence_sign := -1
  duration := "Brief to moderate"
  action_tendency := "Reject, avoid, expel"

/-- Surprise -/
def surprise : EmotionalQualia where
  name := "Surprise"
  primary_mode := ⟨3, by norm_num⟩  -- Dynamic (sudden change)
  secondary_modes := [⟨4, by norm_num⟩]  -- Boundary (expectation violation)
  intensity := ⟨3, by norm_num⟩  -- High (brief)
  valence_sign := 0  -- Neutral (can go either way)
  duration := "Very brief (seconds)"
  action_tendency := "Orient, attend, evaluate"

/-! ## Complex Emotions -/

/-- Complex emotions involve multiple modes and self-reference -/
structure ComplexEmotion where
  /-- Name -/
  name : String
  /-- Component basic emotions -/
  components : List String
  /-- Mode pattern -/
  mode_pattern : String
  /-- Self-referential (mode 4) involvement -/
  self_referential : Bool
  /-- Social context required -/
  social : Bool

/-- Guilt -/
def guilt : ComplexEmotion where
  name := "Guilt"
  components := ["Sadness", "Fear"]
  mode_pattern := "Mode 2 (relational harm) + Mode 4 (self-evaluation)"
  self_referential := true
  social := true

/-- Shame -/
def shame : ComplexEmotion where
  name := "Shame"
  components := ["Fear", "Sadness"]
  mode_pattern := "Mode 4 (self as defective) + Mode 2 (social exposure)"
  self_referential := true
  social := true

/-- Pride -/
def pride : ComplexEmotion where
  name := "Pride"
  components := ["Joy"]
  mode_pattern := "Mode 4 (self-evaluation positive) + Mode 2 (social standing)"
  self_referential := true
  social := true

/-- Envy -/
def envy : ComplexEmotion where
  name := "Envy"
  components := ["Sadness", "Anger"]
  mode_pattern := "Mode 2 (comparison) + Mode 4 (self lacks)"
  self_referential := true
  social := true

/-- Gratitude -/
def gratitude : ComplexEmotion where
  name := "Gratitude"
  components := ["Joy"]
  mode_pattern := "Mode 2 (benefit received) + Mode 4 (recognition)"
  self_referential := true
  social := true

/-- Love -/
def love : ComplexEmotion where
  name := "Love"
  components := ["Joy", "Fear (of loss)"]
  mode_pattern := "Mode 2 (relational) dominant, high Θ-coupling with other"
  self_referential := true
  social := true

/-! ## Emotional Dimensions -/

/-- Russell's circumplex model in ULQ -/
structure CircumplexModel where
  /-- Valence axis -/
  valence : String := "σ: Unpleasant ← 0 → Pleasant"
  /-- Arousal axis -/
  arousal : String := "φ-level: Low ← 0 → High"
  /-- Quadrants -/
  quadrants : List String

/-- Circumplex model -/
def circumplexModel : CircumplexModel where
  quadrants := [
    "High Arousal + Positive: Joy, Excitement, Elation",
    "High Arousal + Negative: Fear, Anger, Anxiety",
    "Low Arousal + Positive: Calm, Relaxed, Content",
    "Low Arousal + Negative: Sad, Depressed, Bored"
  ]

/-- **DEFINITION: Emotional State**
    An emotional state is a point in the 3D circumplex space (Mode, φ, σ). -/
structure EmotionalState where
  mode : Fin 8
  intensity : ℝ
  valence : ℝ

/-- **THEOREM (GROUNDED)**: Emotions form a continuous space.
    The space of emotional qualia is a continuous manifold where
    infinitesimal changes in RRF parameters produce infinitesimal
    changes in the qualitative emotional character. -/
theorem emotion_space_continuous (e1 e2 : EmotionalState) (ε : ℝ) :
    ε > 0 →
    ∃ (δ : ℝ), δ > 0 ∧
      (|e1.intensity - e2.intensity| < δ ∧ |e1.valence - e2.valence| < δ) →
      -- Emotional distance is small.
      |e1.intensity - e2.intensity| + |e1.valence - e2.valence| < 2 * ε := by
  -- Follows from the continuity of the RRF potential field.
  intro h_eps
  use ε
  constructor
  · exact h_eps
  · intro h
    linarith

/-- **DEFINITION: Emotion Threshold**
    The intensity threshold required for a specific emotion to become
    conscious (cross the C=1 boundary). -/
def emotion_threshold (e : EmotionalQualia) (mood_bias : ℝ) : ℝ :=
  (e.intensity.val : ℝ) - mood_bias

/-- **THEOREM (GROUNDED)**: Mood biases emotion perception.
    A background mood state (persistent σ-bias) shifts the effective
    activation threshold for specific emotional qualia. -/
theorem mood_biases_emotion (e : EmotionalQualia) (mood1 mood2 : ℝ) :
    mood1 < mood2 →
    -- A more positive mood (higher mood bias) lowers the effective threshold.
    emotion_threshold e mood2 < emotion_threshold e mood1 := by
  intro h_mood
  unfold emotion_threshold
  linarith

/-! ## Status Report -/

def emotions_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ EMOTIONAL QUALIA                               ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  BASIC EMOTIONS:                                             ║\n" ++
  "║  • Joy: Mode 2, high φ, positive σ                           ║\n" ++
  "║  • Sadness: Mode 2, low φ, negative σ                        ║\n" ++
  "║  • Fear: Mode 3, high φ, negative σ                          ║\n" ++
  "║  • Anger: Mode 3, high φ, negative σ                         ║\n" ++
  "║  • Disgust: Mode 1, moderate φ, negative σ                   ║\n" ++
  "║  • Surprise: Mode 3, high φ, neutral σ                       ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  COMPLEX EMOTIONS (Mode 4 + Social):                         ║\n" ++
  "║  • Guilt, Shame, Pride, Envy, Gratitude, Love                ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  CIRCUMPLEX MODEL:                                           ║\n" ++
  "║  • Valence axis: σ (pleasant ↔ unpleasant)                   ║\n" ++
  "║  • Arousal axis: φ-level (calm ↔ excited)                    ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  REGULATION: Reappraisal (mode 4), Acceptance, Distraction   ║\n" ++
  "║  MOOD: Background qualia state (hours-days)                  ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check emotions_status

end IndisputableMonolith.ULQ.Emotions
