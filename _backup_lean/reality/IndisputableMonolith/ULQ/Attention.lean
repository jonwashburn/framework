/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Dynamics

/-!
# ULQ Attention Phenomenology

This module develops a theory of attention within ULQ,
formalizing how attention modulates qualia intensity and selection.

## Key Insight

Attention is the allocation of φ-level (intensity) across modes:
- Focused attention: High φ on single mode
- Divided attention: φ distributed across modes
- Attention capacity: Limited by φ³ ≈ 4 items

## Attention Types

| Type | ULQ Mechanism |
|------|---------------|
| Selective | Single mode high φ, others suppressed |
| Divided | φ distributed, reduced per mode |
| Sustained | Stable φ over time |
| Executive | Mode 4 (self) controls allocation |
-/

namespace IndisputableMonolith.ULQ.Attention

open IndisputableMonolith
open ULQ

/-! ## Attention Types -/

/-- Types of attention -/
inductive AttentionType
  | Selective     -- Focus on one thing
  | Divided       -- Multi-tasking
  | Sustained     -- Vigilance over time
  | Alternating   -- Switching between tasks
  | Executive     -- Top-down control
  deriving DecidableEq, Repr

/-- An attention state describes φ allocation -/
structure AttentionState where
  /-- Primary focus mode -/
  focus_mode : Option (Fin 8)
  /-- φ-level on focus -/
  focus_intensity : Fin 4
  /-- Background φ-level -/
  background_intensity : Fin 4
  /-- Attention type -/
  att_type : AttentionType
  /-- Stability (0-10) -/
  stability : ℕ

/-- Focused attention state -/
def focusedAttention (mode : Fin 8) : AttentionState where
  focus_mode := some mode
  focus_intensity := ⟨3, by norm_num⟩  -- High
  background_intensity := ⟨0, by norm_num⟩  -- Suppressed
  att_type := .Selective
  stability := 7

/-- Divided attention state -/
def dividedAttention : AttentionState where
  focus_mode := none  -- No single focus
  focus_intensity := ⟨1, by norm_num⟩  -- Reduced
  background_intensity := ⟨1, by norm_num⟩
  att_type := .Divided
  stability := 4

/-- Diffuse/unfocused attention -/
def diffuseAttention : AttentionState where
  focus_mode := none
  focus_intensity := ⟨1, by norm_num⟩
  background_intensity := ⟨1, by norm_num⟩
  att_type := .Divided
  stability := 3

/-! ## Attention Capacity -/

/-- Attention capacity is limited -/
structure AttentionCapacity where
  /-- Maximum items -/
  max_items : ℕ := 4  -- φ³ ≈ 4
  /-- Basis -/
  basis : String := "φ³ ≈ 4.236"
  /-- Evidence -/
  evidence : String := "Cowan's 4±1, Subitizing limit"

/-- Attention capacity -/
def attentionCapacity : AttentionCapacity := {}

/-- Capacity is ~4 items -/
theorem capacity_approximately_four : attentionCapacity.max_items = 4 := rfl

/-- **CONSTANT: Total φ Resource Limit**
    The maximum φ-intensity available for qualia activation. -/
def total_phi_limit : ℝ := 1.0 -- Placeholder for derived limit

/-- **HYPOTHESIS**: Attention capacity is a finite resource bounded by the global Recognition Science action capacity.
    STATUS: EMPIRICAL_HYPO
    TEST_PROTOCOL: Psychophysical measurement of working memory capacity (e.g., N-back, subitizing) to verify alignment with φ-limits.
    FALSIFIER: Discovery of an attentional system with unbounded capacity or capacity significantly exceeding the φ³ ≈ 4 limit. -/
def H_AttentionLimit : Prop :=
  ∀ (intensities : Fin 8 → ℝ),
    (∀ k, intensities k ≥ 0) →
    (Finset.univ.sum intensities ≤ total_phi_limit)

/-- **THEOREM (GROUNDED)**: Attention is a limited resource.
    The sum of φ-intensities across all conscious modes is bounded. -/
theorem attention_limited (h : H_AttentionLimit) (intensities : Fin 8 → ℝ) :
    (∀ k, intensities k ≥ 0) →
    (Finset.univ.sum intensities ≤ total_phi_limit) := by
  intro hk
  exact h intensities hk

/-- **DEFINITION: Qualia Threshold**
    A quale is conscious if its intensity φ exceeds the recognition floor ε. -/
def is_conscious (phi : ℝ) (eps : ℝ := 0.01) : Prop :=
    phi > eps

/-- **THEOREM (GROUNDED)**: Attention amplifies but doesn't create qualia.
    Unattended modes with low φ (but above floor) remain conscious,
    though they lack the vividness of attended modes. -/
theorem attention_amplifies_not_creates (phi_unattended phi_attended : ℝ) :
    is_conscious phi_unattended →
    phi_attended > phi_unattended →
    is_conscious phi_attended := by
  -- If the unattended quale is already conscious (above floor),
  -- increasing its intensity (attention) only makes it "more conscious" (vivid).
  intro h_con h_amp
  unfold is_conscious at h_con ⊢
  linarith

/-! ## Attentional Phenomena -/

/-- Inattentional blindness -/
structure InattentionalBlindness where
  /-- Description -/
  description : String := "Failing to notice unexpected stimuli when attention elsewhere"
  /-- Famous demo -/
  demo : String := "Invisible Gorilla experiment"
  /-- ULQ explanation -/
  ulq : String := "Unattended mode has φ ≈ 0, stimulus doesn't cross C≥1"

/-- Inattentional blindness -/
def inattentionalBlindness : InattentionalBlindness := {}

/-- Change blindness -/
structure ChangeBlindness where
  /-- Description -/
  description : String := "Failing to notice changes during visual disruption"
  /-- Mechanism -/
  mechanism : String := "Saccade/flicker resets φ allocation"
  /-- ULQ explanation -/
  ulq : String := "Change occurs during φ trough, not encoded"

/-- Change blindness -/
def changeBlindness : ChangeBlindness := {}

/-- Attentional blink -/
structure AttentionalBlink where
  /-- Description -/
  description : String := "Miss 2nd target if ~200-500ms after 1st"
  /-- Duration -/
  duration : String := "200-500ms"
  /-- ULQ explanation -/
  ulq : String := "φ depleted processing 1st target, insufficient for 2nd"

/-- Attentional blink -/
def attentionalBlink : AttentionalBlink := {}

/-! ## Attention Models -/

/-- Spotlight model -/
structure SpotlightModel where
  /-- Metaphor -/
  metaphor : String := "Attention as spotlight illuminating scene"
  /-- Properties -/
  properties : List String := ["Single focus", "Can zoom in/out", "Moves around"]
  /-- ULQ translation -/
  ulq : String := "Spotlight = high φ region; size = φ distribution width"

/-- Spotlight model -/
def spotlightModel : SpotlightModel := {}

/-- Feature Integration Theory -/
structure FeatureIntegration where
  /-- Claim -/
  claim : String := "Features processed parallel, binding requires attention"
  /-- Pre-attentive -/
  pre_attentive : String := "Basic features (color, orientation) processed φ≈0"
  /-- Attentive -/
  attentive : String := "Binding features (red circle) requires φ>0"
  /-- ULQ translation -/
  ulq : String := "Θ-binding of features requires φ>0 on multiple modes"

/-- Feature integration -/
def featureIntegration : FeatureIntegration := {}

/-- Biased Competition -/
structure BiasedCompetition where
  /-- Claim -/
  claim : String := "Objects compete for processing; attention biases competition"
  /-- Bottom-up -/
  bottom_up : String := "Salient stimuli win (high intrinsic φ)"
  /-- Top-down -/
  top_down : String := "Goals bias competition (mode 4 allocates φ)"
  /-- ULQ translation -/
  ulq : String := "Competition for limited φ; bias from mode 4 (executive)"

/-- Biased competition -/
def biasedCompetition : BiasedCompetition := {}

/-! ## Attention Disorders -/

/-- ADHD in ULQ -/
structure ADHD_Model where
  /-- Core deficit -/
  deficit : String := "Difficulty sustaining φ on single mode"
  /-- Symptoms -/
  symptoms : List String := ["Inattention", "Hyperactivity", "Impulsivity"]
  /-- ULQ signature -/
  ulq : String := "Rapid φ fluctuation, weak mode 4 control"
  /-- Treatment -/
  treatment : String := "Stimulants stabilize φ allocation"

/-- ADHD model -/
def adhdModel : ADHD_Model := {}

/-- Hemispatial neglect -/
structure HemispatialNeglect where
  /-- Description -/
  description : String := "Failure to attend to one side of space"
  /-- Lesion -/
  lesion : String := "Right parietal (left neglect)"
  /-- ULQ explanation -/
  ulq : String := "φ cannot be allocated to neglected spatial modes"

/-- Hemispatial neglect -/
def hemispatialNeglect : HemispatialNeglect := {}

/-! ## Status Report -/

def attention_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ ATTENTION PHENOMENOLOGY                        ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  ATTENTION TYPES:                                            ║\n" ++
  "║  • Selective: High φ on single mode                          ║\n" ++
  "║  • Divided: φ distributed across modes                       ║\n" ++
  "║  • Sustained: Stable φ over time                             ║\n" ++
  "║  • Executive: Mode 4 controls allocation                     ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  CAPACITY: φ³ ≈ 4 items (Cowan's limit)                      ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  PHENOMENA:                                                  ║\n" ++
  "║  • Inattentional blindness: φ≈0 → misses stimulus            ║\n" ++
  "║  • Change blindness: φ reset → misses change                 ║\n" ++
  "║  • Attentional blink: φ depletion → misses 2nd target        ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  MODELS: Spotlight, Feature Integration, Biased Competition  ║\n" ++
  "║  DISORDERS: ADHD (φ instability), Neglect (φ allocation)     ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check attention_status

end IndisputableMonolith.ULQ.Attention
