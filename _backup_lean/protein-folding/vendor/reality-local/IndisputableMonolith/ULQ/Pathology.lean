/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Dynamics
import IndisputableMonolith.ULQ.Binding

/-!
# ULQ Qualia Pathology

This module models psychiatric and neurological conditions as
disturbances in the ULQ qualia structure.

## Key Insight

Mental disorders can be understood as specific disruptions to:
1. **Mode structure** (perception disorders)
2. **Intensity levels** (attention disorders)
3. **Valence dynamics** (mood disorders)
4. **Temporal quality** (dissociation)
5. **Θ-binding** (fragmentation disorders)

## Clinical Implications

ULQ provides a principled basis for:
- Classifying disorders by which parameter is affected
- Predicting symptoms from parameter disruptions
- Designing interventions targeting specific parameters
-/

namespace IndisputableMonolith.ULQ.Pathology

open IndisputableMonolith
open ULQ

/-! ## Disorder Classification -/

/-- Types of qualia parameter disruptions -/
inductive DisruptionType
  | ModeDistortion      -- Perception/hallucination
  | IntensityDysregulation -- Attention problems
  | ValenceImbalance    -- Mood disorders
  | TemporalDisturbance -- Dissociation
  | BindingFailure      -- Fragmentation
  | ThresholdShift      -- Consciousness level
  deriving DecidableEq, Repr

/-- A qualia pathology specification -/
structure QualiaPathology where
  /-- Name of condition -/
  name : String
  /-- Primary disruption type -/
  primary_disruption : DisruptionType
  /-- Secondary disruptions -/
  secondary_disruptions : List DisruptionType
  /-- Affected parameters -/
  description : String

/-! ## Mode Distortions (Perception Disorders) -/

/-- Schizophrenia: mode mixing and false mode activation -/
def schizophrenia : QualiaPathology where
  name := "Schizophrenia"
  primary_disruption := .ModeDistortion
  secondary_disruptions := [.BindingFailure, .ValenceImbalance]
  description := "Spurious mode activations (hallucinations) + binding breakdown"

/-- Autism Spectrum: altered mode sensitivity -/
def autismSpectrum : QualiaPathology where
  name := "Autism Spectrum"
  primary_disruption := .ModeDistortion
  secondary_disruptions := [.IntensityDysregulation]
  description := "Enhanced sensitivity in some modes, reduced in others"

/-- Synesthesia: mode cross-activation -/
def synesthesia : QualiaPathology where
  name := "Synesthesia"
  primary_disruption := .ModeDistortion
  secondary_disruptions := []
  description := "Modes activate together that normally don't (e.g., sound→color)"

/-! ## Intensity Dysregulation (Attention Disorders) -/

/-- ADHD: intensity fluctuation and filtering problems -/
def adhd : QualiaPathology where
  name := "ADHD"
  primary_disruption := .IntensityDysregulation
  secondary_disruptions := [.TemporalDisturbance]
  description := "Intensity levels fluctuate; can't maintain stable focus"

/-- Hyperfocus: intensity stuck at maximum -/
def hyperfocus : QualiaPathology where
  name := "Hyperfocus"
  primary_disruption := .IntensityDysregulation
  secondary_disruptions := []
  description := "Single mode stuck at φ³ intensity; others suppressed"

/-! ## Valence Imbalance (Mood Disorders) -/

/-- Depression: negative valence bias -/
def depression : QualiaPathology where
  name := "Major Depression"
  primary_disruption := .ValenceImbalance
  secondary_disruptions := [.IntensityDysregulation]
  description := "σ consistently negative; hedonic flattening"

/-- Mania: positive valence excess -/
def mania : QualiaPathology where
  name := "Mania"
  primary_disruption := .ValenceImbalance
  secondary_disruptions := [.IntensityDysregulation, .TemporalDisturbance]
  description := "σ consistently positive; hedonic amplification"

/-- Bipolar: valence oscillation -/
def bipolar : QualiaPathology where
  name := "Bipolar Disorder"
  primary_disruption := .ValenceImbalance
  secondary_disruptions := [.TemporalDisturbance]
  description := "σ oscillates between extremes"

/-- Anhedonia: valence flattening -/
def anhedonia : QualiaPathology where
  name := "Anhedonia"
  primary_disruption := .ValenceImbalance
  secondary_disruptions := []
  description := "σ ≈ 0 regardless of stimuli; no pleasure or pain"

/-! ## Temporal Disturbances (Dissociation) -/

/-- Dissociation: temporal fragmentation -/
def dissociation : QualiaPathology where
  name := "Dissociative Disorder"
  primary_disruption := .TemporalDisturbance
  secondary_disruptions := [.BindingFailure]
  description := "τ-offset disrupted; experiences feel unreal or distant"

/-- Depersonalization: self-reference temporal shift -/
def depersonalization : QualiaPathology where
  name := "Depersonalization"
  primary_disruption := .TemporalDisturbance
  secondary_disruptions := [.ModeDistortion]
  description := "Self-referential qualia (mode 4) feel temporally displaced"

/-- PTSD: temporal intrusion -/
def ptsd : QualiaPathology where
  name := "PTSD"
  primary_disruption := .TemporalDisturbance
  secondary_disruptions := [.ValenceImbalance, .IntensityDysregulation]
  description := "Past qualia intrude on present (flashbacks)"

/-! ## Binding Failures (Fragmentation) -/

/-- Binding failure: Θ-coupling breakdown -/
def bindingFailure : QualiaPathology where
  name := "Binding Failure"
  primary_disruption := .BindingFailure
  secondary_disruptions := []
  description := "Θ-coupling weakened; experiences don't unify"

/-- DID: multiple Θ-phases -/
def dissociativeIdentity : QualiaPathology where
  name := "Dissociative Identity Disorder"
  primary_disruption := .BindingFailure
  secondary_disruptions := [.TemporalDisturbance]
  description := "Multiple distinct Θ-phases; separate experiential streams"

/-! ## Threshold Shifts (Consciousness Level) -/

/-- Coma: C < 1 globally -/
def coma : QualiaPathology where
  name := "Coma"
  primary_disruption := .ThresholdShift
  secondary_disruptions := []
  description := "Global C < 1; no qualia actualize"

/-- Delirium: C threshold fluctuating -/
def delirium : QualiaPathology where
  name := "Delirium"
  primary_disruption := .ThresholdShift
  secondary_disruptions := [.ModeDistortion, .BindingFailure]
  description := "C threshold unstable; consciousness flickers"

/-! ## Pathology Metrics -/

/-- Severity scale for pathology -/
inductive Severity
  | Mild      -- Minor parameter deviation
  | Moderate  -- Noticeable impact on function
  | Severe    -- Major impairment
  | Profound  -- Complete breakdown
  deriving DecidableEq, Repr

/-- Pathology state -/
structure PathologyState where
  /-- The condition -/
  condition : QualiaPathology
  /-- Current severity -/
  severity : Severity
  /-- Affected qualia count -/
  affected_qualia_ratio : ℕ  -- 0-100 percent

/-! ## Treatment Targets -/

/-- Treatment approaches based on disruption type -/
def treatmentTarget (d : DisruptionType) : String :=
  match d with
  | .ModeDistortion => "Stabilize mode activation (antipsychotics target this)"
  | .IntensityDysregulation => "Regulate intensity levels (stimulants/attention training)"
  | .ValenceImbalance => "Rebalance σ-gradient (antidepressants/mood stabilizers)"
  | .TemporalDisturbance => "Restore τ-continuity (grounding techniques)"
  | .BindingFailure => "Strengthen Θ-coupling (integration therapy)"
  | .ThresholdShift => "Restore C threshold (medical intervention)"

/-- Intervention model -/
structure Intervention where
  /-- Name of intervention -/
  name : String
  /-- Target disruption -/
  target : DisruptionType
  /-- Expected effect -/
  effect : String

/-- Example interventions -/
def meditationIntervention : Intervention where
  name := "Meditation"
  target := .ValenceImbalance
  effect := "Moves σ toward 0 (equilibrium)"

def emdrIntervention : Intervention where
  name := "EMDR"
  target := .TemporalDisturbance
  effect := "Reprocesses stuck temporal patterns"

def antipsychoticIntervention : Intervention where
  name := "Antipsychotic medication"
  target := .ModeDistortion
  effect := "Reduces spurious mode activations"

/-! ## Complete Pathology Catalog -/

/-- All defined pathologies -/
def pathologyCatalog : List QualiaPathology :=
  [schizophrenia, autismSpectrum, synesthesia,
   adhd, hyperfocus,
   depression, mania, bipolar, anhedonia,
   dissociation, depersonalization, ptsd,
   bindingFailure, dissociativeIdentity,
   coma, delirium]

/-- Catalog size -/
theorem catalog_size : pathologyCatalog.length = 16 := by native_decide

/-! ## Status Report -/

def pathology_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ QUALIA PATHOLOGY                               ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  DISRUPTION TYPES:                                           ║\n" ++
  "║  • Mode Distortion: hallucinations, synesthesia              ║\n" ++
  "║  • Intensity Dysregulation: ADHD, hyperfocus                 ║\n" ++
  "║  • Valence Imbalance: depression, mania, bipolar             ║\n" ++
  "║  • Temporal Disturbance: dissociation, PTSD                  ║\n" ++
  "║  • Binding Failure: fragmentation, DID                       ║\n" ++
  "║  • Threshold Shift: coma, delirium                           ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  16 CONDITIONS MODELED                                       ║\n" ++
  "║                                                              ║\n" ++
  "║  KEY INSIGHT:                                                ║\n" ++
  "║  Mental disorders = specific ULQ parameter disruptions.      ║\n" ++
  "║  This provides principled basis for classification,          ║\n" ++
  "║  symptom prediction, and targeted intervention.              ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check pathology_status

end IndisputableMonolith.ULQ.Pathology
