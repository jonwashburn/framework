/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Taxonomy
import IndisputableMonolith.ULQ.Memory

/-!
# ULQ Developmental Qualia

This module formalizes how qualia develop across the lifespan,
from prenatal to elderly stages.

## Key Insight

Qualia don't "emerge" gradually. Once C≥1 is crossed, full qualia exist.
What develops is:
1. **C threshold crossing** - When it first happens
2. **Mode differentiation** - Which modes become accessible
3. **Intensity regulation** - Control over attention
4. **Valence stability** - Emotional regulation
5. **Θ-binding strength** - Unity of experience

## Developmental Stages

| Stage | C Level | Primary Development |
|-------|---------|---------------------|
| Prenatal | ~0.5 | Approaching threshold |
| Infant | 1-2 | Basic mode access |
| Toddler | 2-3 | Mode differentiation |
| Child | 3-5 | Intensity regulation |
| Adolescent | 5-8 | Valence integration |
| Adult | 8-10 | Full integration |
| Elderly | 8-10 | Selective decline |
-/

namespace IndisputableMonolith.ULQ.Developmental

open IndisputableMonolith
open ULQ

/-! ## Developmental Stages -/

/-- Life stages for qualia development -/
inductive DevelopmentalStage
  | Prenatal     -- Before birth
  | Infant       -- 0-2 years
  | Toddler      -- 2-5 years
  | Child        -- 5-12 years
  | Adolescent   -- 12-18 years
  | Adult        -- 18-65 years
  | Elderly      -- 65+ years
  deriving DecidableEq, Repr

/-- Estimated C level at each stage -/
def stageCLevel (s : DevelopmentalStage) : String :=
  match s with
  | .Prenatal => "C ≈ 0.3-0.8 (approaching threshold)"
  | .Infant => "C ≈ 1-2 (just crossed threshold)"
  | .Toddler => "C ≈ 2-3 (expanding)"
  | .Child => "C ≈ 3-5 (consolidating)"
  | .Adolescent => "C ≈ 5-8 (integrating)"
  | .Adult => "C ≈ 8-10 (peak)"
  | .Elderly => "C ≈ 6-10 (variable decline)"

/-! ## Qualia Profile at Each Stage -/

/-- Qualia profile for a developmental stage -/
structure StageQualiaProfile where
  /-- Stage -/
  stage : DevelopmentalStage
  /-- Accessible modes (which of the 4 families) -/
  accessible_modes : List Taxonomy.QualiaFamily
  /-- Maximum intensity achievable -/
  max_intensity : Fin 4
  /-- Valence regulation ability (0-100) -/
  valence_regulation : ℕ
  /-- Θ-binding strength (0-100) -/
  binding_strength : ℕ
  /-- Description -/
  description : String

/-- Prenatal profile -/
def prenatalProfile : StageQualiaProfile where
  stage := .Prenatal
  accessible_modes := [.Primordial]  -- Basic presence only
  max_intensity := 1
  valence_regulation := 0
  binding_strength := 20
  description := "Primarily undifferentiated awareness, some basic valence"

/-- Infant profile -/
def infantProfile : StageQualiaProfile where
  stage := .Infant
  accessible_modes := [.Primordial, .Dynamic]
  max_intensity := 2
  valence_regulation := 10
  binding_strength := 40
  description := "Basic sensory qualia, strong but unregulated emotions"

/-- Toddler profile -/
def toddlerProfile : StageQualiaProfile where
  stage := .Toddler
  accessible_modes := [.Primordial, .Relational, .Dynamic]
  max_intensity := 3
  valence_regulation := 25
  binding_strength := 60
  description := "Spatial awareness emerges, emotional storms common"

/-- Child profile -/
def childProfile : StageQualiaProfile where
  stage := .Child
  accessible_modes := [.Primordial, .Relational, .Dynamic, .SelfReferential]
  max_intensity := 3
  valence_regulation := 50
  binding_strength := 75
  description := "All modes accessible, developing self-reflection"

/-- Adolescent profile -/
def adolescentProfile : StageQualiaProfile where
  stage := .Adolescent
  accessible_modes := [.Primordial, .Relational, .Dynamic, .SelfReferential]
  max_intensity := 3
  valence_regulation := 60
  binding_strength := 85
  description := "Intense self-referential qualia, identity formation"

/-- Adult profile -/
def adultProfile : StageQualiaProfile where
  stage := .Adult
  accessible_modes := [.Primordial, .Relational, .Dynamic, .SelfReferential]
  max_intensity := 3
  valence_regulation := 80
  binding_strength := 95
  description := "Full integration, stable valence regulation"

/-- Elderly profile -/
def elderlyProfile : StageQualiaProfile where
  stage := .Elderly
  accessible_modes := [.Primordial, .Relational, .Dynamic, .SelfReferential]
  max_intensity := 2  -- Some intensity decline
  valence_regulation := 85  -- Often improved!
  binding_strength := 80  -- Some decline
  description := "Reduced intensity, improved valence regulation (positivity effect)"

/-! ## Developmental Milestones -/

/-- Key qualia milestones -/
inductive QualiaMilestone
  | FirstThresholdCrossing   -- C≥1 for first time
  | ModeDiscrimination       -- Can distinguish modes
  | IntensityControl         -- Can modulate attention
  | ValenceRegulation        -- Can regulate emotions
  | SelfReflection           -- Mode 4 online
  | TemporalExtension        -- Past/future qualia
  | FullIntegration          -- All systems unified
  deriving DecidableEq, Repr

/-- Typical age for each milestone -/
def milestoneAge (m : QualiaMilestone) : String :=
  match m with
  | .FirstThresholdCrossing => "~24-28 weeks gestation"
  | .ModeDiscrimination => "~3-6 months"
  | .IntensityControl => "~2-3 years"
  | .ValenceRegulation => "~5-7 years"
  | .SelfReflection => "~4-5 years (mirror test)"
  | .TemporalExtension => "~3-4 years (autobiographical memory)"
  | .FullIntegration => "~18-25 years (prefrontal maturation)"

/-! ## Critical Periods -/

/-- Critical periods for qualia development -/
structure CriticalPeriod where
  /-- What develops -/
  development : String
  /-- Start age -/
  start_age : String
  /-- End age -/
  end_age : String
  /-- Consequence of deprivation -/
  deprivation_effect : String

/-- Visual qualia critical period -/
def visualCriticalPeriod : CriticalPeriod where
  development := "Visual mode differentiation"
  start_age := "Birth"
  end_age := "~8 years"
  deprivation_effect := "Permanent visual qualia impairment if deprived"

/-- Language qualia critical period -/
def languageCriticalPeriod : CriticalPeriod where
  development := "Language-qualia mapping"
  start_age := "~6 months"
  end_age := "~12 years"
  deprivation_effect := "Reduced ability to verbalize qualia"

/-- Social qualia critical period -/
def socialCriticalPeriod : CriticalPeriod where
  development := "Empathic Θ-coupling"
  start_age := "Birth"
  end_age := "~3 years"
  deprivation_effect := "Impaired qualia sharing (attachment disorders)"

/-! ## Aging and Qualia -/

/-- Age-related qualia changes -/
structure AgingEffects where
  /-- Intensity changes -/
  intensity_effect : String := "Gradual decline in peak intensity"
  /-- Valence changes -/
  valence_effect : String := "Positivity effect: bias toward pleasant qualia"
  /-- Binding changes -/
  binding_effect : String := "Some Θ-coupling decline (tip-of-tongue phenomena)"
  /-- Temporal changes -/
  temporal_effect : String := "Subjective time acceleration"

/-- Aging effects on qualia -/
def agingEffects : AgingEffects := {}

/-- **POSITIVITY EFFECT**: Elderly show preferential processing of positive qualia.

    This is not cognitive decline but adaptive regulation:
    - Reduced amygdala response to negative stimuli
    - Increased prefrontal regulation of valence
    - Result: σ-gradient biased toward positive -/
def positivity_effect_hypothesis : Prop :=
  ∀ (profile : StageQualiaProfile),
    profile.stage = .Elderly →
    profile.valence_regulation ≥ 80

/-! ## Developmental Disorders -/

/-- Disorders affecting qualia development -/
structure DevelopmentalDisorder where
  /-- Name -/
  name : String
  /-- Affected aspect -/
  affected_aspect : String
  /-- Stage of impact -/
  critical_stage : DevelopmentalStage
  /-- ULQ characterization -/
  ulq_description : String

/-- Autism affects mode development -/
def autismDevelopment : DevelopmentalDisorder where
  name := "Autism Spectrum"
  affected_aspect := "Mode differentiation and Θ-coupling"
  critical_stage := .Infant
  ulq_description := "Altered mode sensitivity, reduced social Θ-coupling"

/-- ADHD affects intensity regulation -/
def adhdDevelopment : DevelopmentalDisorder where
  name := "ADHD"
  affected_aspect := "Intensity regulation"
  critical_stage := .Child
  ulq_description := "Delayed development of intensity control mechanisms"

/-- Attachment disorders affect binding -/
def attachmentDisorder : DevelopmentalDisorder where
  name := "Reactive Attachment Disorder"
  affected_aspect := "Empathic Θ-coupling"
  critical_stage := .Infant
  ulq_description := "Impaired development of inter-agent qualia sharing"

/-! ## Status Report -/

def developmental_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ DEVELOPMENTAL QUALIA                           ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  STAGES:                                                     ║\n" ++
  "║  • Prenatal: C≈0.5, primordial only                          ║\n" ++
  "║  • Infant: C≈1-2, basic modes                                ║\n" ++
  "║  • Child: C≈3-5, all modes, developing regulation            ║\n" ++
  "║  • Adult: C≈8-10, full integration                           ║\n" ++
  "║  • Elderly: C≈6-10, positivity effect                        ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  KEY INSIGHT:                                                ║\n" ++
  "║  Qualia don't emerge gradually. Once C≥1, full qualia exist. ║\n" ++
  "║  What develops: mode access, intensity control, regulation.  ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  CRITICAL PERIODS:                                           ║\n" ++
  "║  • Visual: birth to ~8 years                                 ║\n" ++
  "║  • Language: ~6mo to ~12 years                               ║\n" ++
  "║  • Social: birth to ~3 years                                 ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check developmental_status

end IndisputableMonolith.ULQ.Developmental
