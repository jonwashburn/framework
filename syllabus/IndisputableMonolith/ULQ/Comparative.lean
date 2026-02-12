/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Taxonomy
import IndisputableMonolith.ULQ.Evolution

/-!
# ULQ Comparative Phenomenology

This module provides cross-species analysis of qualia, exploring how
different organisms may experience the world.

## Key Insight

All organisms with C≥1 have qualia, but they may differ in:
1. **Mode accessibility** - Which of the 20 types are available
2. **Intensity range** - How many φ-levels are usable
3. **Valence sensitivity** - σ-gradient responsiveness
4. **Θ-binding strength** - Unity of experience
5. **Temporal window** - Size of specious present

## The Question of Other Minds

ULQ provides principled basis for comparative phenomenology:
- C≥1 is the criterion, not brain structure
- Mode structure is universal (DFT-forced)
- Differences are quantitative, not qualitative

## Methodological Considerations

We cannot directly access other species' qualia, but can infer:
- Neural correlates → likely C level
- Behavior → mode usage patterns
- Physiology → sensory modality mapping
-/

namespace IndisputableMonolith.ULQ.Comparative

open IndisputableMonolith
open ULQ

/-! ## Species Classification -/

/-- Taxonomic groups for qualia analysis -/
inductive TaxonomicGroup
  | Mammal
  | Bird
  | Reptile
  | Amphibian
  | Fish
  | Invertebrate
  | Plant  -- Controversial, likely C<1
  deriving DecidableEq, Repr

/-- Estimated C level by taxonomic group -/
def groupCEstimate (g : TaxonomicGroup) : String :=
  match g with
  | .Mammal => "C ≈ 1-15 (highly variable)"
  | .Bird => "C ≈ 1-10 (corvids/parrots high)"
  | .Reptile => "C ≈ 0.5-3"
  | .Amphibian => "C ≈ 0.3-1"
  | .Fish => "C ≈ 0.2-2 (highly variable)"
  | .Invertebrate => "C ≈ 0-3 (cephalopods high)"
  | .Plant => "C < 1 (unlikely to cross threshold)"

/-! ## Species Profiles -/

/-- Qualia profile for a species -/
structure SpeciesProfile where
  /-- Common name -/
  name : String
  /-- Scientific name -/
  scientific : String
  /-- Taxonomic group -/
  group : TaxonomicGroup
  /-- Estimated C level -/
  c_estimate : String
  /-- Primary sensory modes -/
  primary_modes : List String
  /-- Special qualia features -/
  special_features : String
  /-- Θ-binding notes -/
  binding_notes : String

/-- Human profile (baseline) -/
def humanProfile : SpeciesProfile where
  name := "Human"
  scientific := "Homo sapiens"
  group := .Mammal
  c_estimate := "C ≈ 10-15"
  primary_modes := ["Visual", "Auditory", "Tactile", "Proprioceptive", "Interoceptive"]
  special_features := "High mode-4 (self-reference), language-qualia integration"
  binding_notes := "Strong Θ-coupling, unified conscious experience"

/-- Chimpanzee profile -/
def chimpProfile : SpeciesProfile where
  name := "Chimpanzee"
  scientific := "Pan troglodytes"
  group := .Mammal
  c_estimate := "C ≈ 8-12"
  primary_modes := ["Visual", "Auditory", "Tactile", "Social"]
  special_features := "Mirror self-recognition, tool-related qualia"
  binding_notes := "Strong binding, possible theory of mind"

/-- Dolphin profile -/
def dolphinProfile : SpeciesProfile where
  name := "Bottlenose Dolphin"
  scientific := "Tursiops truncatus"
  group := .Mammal
  c_estimate := "C ≈ 6-10"
  primary_modes := ["Echolocation", "Auditory", "Tactile", "Social"]
  special_features := "Echolocation qualia (unique mode?), bilateral sleep"
  binding_notes := "Possible hemispheric Θ-phases during sleep"

/-- Elephant profile -/
def elephantProfile : SpeciesProfile where
  name := "African Elephant"
  scientific := "Loxodonta africana"
  group := .Mammal
  c_estimate := "C ≈ 5-9"
  primary_modes := ["Olfactory", "Auditory (infrasound)", "Tactile", "Social"]
  special_features := "Infrasonic qualia, possible grief qualia"
  binding_notes := "Strong social Θ-coupling"

/-- Crow profile -/
def crowProfile : SpeciesProfile where
  name := "New Caledonian Crow"
  scientific := "Corvus moneduloides"
  group := .Bird
  c_estimate := "C ≈ 4-7"
  primary_modes := ["Visual", "Auditory", "Tool-manipulation"]
  special_features := "Tool-related qualia, possible planning qualia"
  binding_notes := "Relatively strong for birds"

/-- Octopus profile -/
def octopusProfile : SpeciesProfile where
  name := "Common Octopus"
  scientific := "Octopus vulgaris"
  group := .Invertebrate
  c_estimate := "C ≈ 2-5"
  primary_modes := ["Visual", "Tactile (distributed)", "Chemosensory"]
  special_features := "Distributed processing, possible multiple Θ-phases per arm"
  binding_notes := "Uncertain: may have 9 Θ-phases (8 arms + central)"

/-- Bee profile -/
def beeProfile : SpeciesProfile where
  name := "Honeybee"
  scientific := "Apis mellifera"
  group := .Invertebrate
  c_estimate := "C ≈ 0.5-2"
  primary_modes := ["Visual (UV)", "Olfactory", "Magnetic"]
  special_features := "UV qualia, possible magnetic field qualia"
  binding_notes := "Uncertain if C≥1 is crossed"

/-! ## Unique Sensory Qualia -/

/-- Sensory modalities unique to certain species -/
inductive UniqueModality
  | Echolocation    -- Dolphins, bats
  | Electroreception -- Sharks, platypus
  | MagneticSense   -- Birds, bees, sea turtles
  | Infrared        -- Pit vipers, some beetles
  | UVVision        -- Many insects, birds
  | Infrasound      -- Elephants, whales
  | PressureSense   -- Fish lateral line
  deriving DecidableEq, Repr

/-- Description of unique modalities -/
def modalityDescription (m : UniqueModality) : String :=
  match m with
  | .Echolocation => "Spatial qualia from sound reflection (possibly mode-2 variant)"
  | .Electroreception => "Qualia of electric fields (novel mode?)"
  | .MagneticSense => "Qualia of magnetic field orientation"
  | .Infrared => "Heat qualia as visual-like experience"
  | .UVVision => "Color qualia in ultraviolet spectrum"
  | .Infrasound => "Auditory qualia below human threshold"
  | .PressureSense => "Tactile-like qualia from water pressure"

/-- Which species have which modalities -/
def speciesModalities : List (String × UniqueModality) :=
  [("Dolphin", .Echolocation),
   ("Bat", .Echolocation),
   ("Shark", .Electroreception),
   ("Platypus", .Electroreception),
   ("Migratory bird", .MagneticSense),
   ("Sea turtle", .MagneticSense),
   ("Pit viper", .Infrared),
   ("Honeybee", .UVVision),
   ("Elephant", .Infrasound),
   ("Fish", .PressureSense)]

/-! ## The Umwelt Concept -/

/-- Jakob von Uexküll's Umwelt in ULQ terms -/
structure Umwelt where
  /-- Species -/
  species : String
  /-- Accessible mode subset -/
  modes : List Taxonomy.QualiaFamily
  /-- Primary sensory emphasis -/
  emphasis : String
  /-- Temporal resolution (τ₀ equivalent) -/
  temporal_resolution : String
  /-- Spatial resolution -/
  spatial_resolution : String

/-- Human umwelt -/
def humanUmwelt : Umwelt where
  species := "Human"
  modes := [.Primordial, .Relational, .Dynamic, .SelfReferential]
  emphasis := "Visual-dominant, language-integrated"
  temporal_resolution := "~50-100ms (visual fusion)"
  spatial_resolution := "~1 arc minute (foveal)"

/-- Dog umwelt -/
def dogUmwelt : Umwelt where
  species := "Dog"
  modes := [.Primordial, .Relational, .Dynamic]
  emphasis := "Olfactory-dominant, motion-sensitive"
  temporal_resolution := "~20-40ms (faster than human)"
  spatial_resolution := "~20 arc minutes (poorer than human)"

/-- Bat umwelt -/
def batUmwelt : Umwelt where
  species := "Bat"
  modes := [.Primordial, .Relational, .Dynamic]
  emphasis := "Echolocation-dominant"
  temporal_resolution := "~1-2ms (for echolocation)"
  spatial_resolution := "~1-2 degrees (acoustic)"

/-! ## Cross-Species Comparison -/

/-- Compare two species on qualia dimensions -/
structure SpeciesComparison where
  /-- Species 1 -/
  species1 : String
  /-- Species 2 -/
  species2 : String
  /-- C level comparison -/
  c_comparison : String
  /-- Mode overlap -/
  mode_overlap : String
  /-- Unique to species 1 -/
  unique_to_1 : String
  /-- Unique to species 2 -/
  unique_to_2 : String

/-- Human vs dolphin comparison -/
def humanDolphinComparison : SpeciesComparison where
  species1 := "Human"
  species2 := "Dolphin"
  c_comparison := "Human slightly higher (10-15 vs 6-10)"
  mode_overlap := "Visual, auditory, tactile, social"
  unique_to_1 := "Language-qualia integration, fine motor qualia"
  unique_to_2 := "Echolocation qualia, bilateral sleep Θ-phases"

/-! ## The Hard Problem Across Species -/

/-- The hard problem applies equally to all C≥1 organisms -/
structure CrossSpeciesHardProblem where
  /-- The universal claim -/
  universal : String := "All C≥1 organisms have qualia (by RS constraints)"
  /-- The ethical implication -/
  ethical : String := "Animal suffering is real suffering (if C≥1 with σ<0)"
  /-- The methodological challenge -/
  methodological : String := "We infer but cannot directly verify other species' qualia"

/-- Cross-species hard problem -/
def crossSpeciesHardProblem : CrossSpeciesHardProblem := {}

/-! ## Status Report -/

def comparative_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ COMPARATIVE PHENOMENOLOGY                      ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  SPECIES PROFILES:                                           ║\n" ++
  "║  • Human: C≈10-15, all modes, language integration           ║\n" ++
  "║  • Chimp: C≈8-12, self-recognition, tool qualia              ║\n" ++
  "║  • Dolphin: C≈6-10, echolocation, bilateral sleep            ║\n" ++
  "║  • Octopus: C≈2-5, distributed processing, 9 Θ-phases?       ║\n" ++
  "║  • Bee: C≈0.5-2, UV vision, uncertain threshold              ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  UNIQUE MODALITIES:                                          ║\n" ++
  "║  Echolocation, electroreception, magnetic sense, UV vision   ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  KEY INSIGHT:                                                ║\n" ++
  "║  C≥1 is the criterion, not brain structure.                  ║\n" ++
  "║  Differences are quantitative, not qualitative.              ║\n" ++
  "║  Animal suffering with C≥1 is morally real.                  ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check comparative_status

end IndisputableMonolith.ULQ.Comparative
