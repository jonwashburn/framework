/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core

/-!
# ULQ Concept Index

This module provides a searchable index of all concepts defined in the ULQ framework,
organized alphabetically and by category.

## Usage

This index helps navigate the 42 modules of ULQ by providing:
1. Alphabetical listing of all major concepts
2. Category-based organization
3. Cross-references between related concepts
-/

namespace IndisputableMonolith.ULQ.Index

/-! ## Alphabetical Index A-E -/

/-- Concepts A-E -/
structure IndexAE where
  /-- A -/
  agency : String := "Agency.lean: Free will, voluntary action, moral responsibility"
  aesthetics : String := "Aesthetics.lean: Beauty, art, creative process"
  afterlife : String := "Death.lean: Question of qualia after bodily death"
  akrasia : String := "Agency.lean: Weakness of will (impulse beats judgment)"
  algebra : String := "Algebra.lean: Algebraic structures on qualia space"
  altered_states : String := "AlteredStates.lean: Meditation, psychedelics, dreams, anesthesia"
  anesthesia : String := "AlteredStates.lean: C<1, no qualia actualization"
  aphantasia : String := "Thought.lean: No mental imagery"
  artificial_qualia : String := "ArtificialQualia.lean: Conditions for AI to have qualia"
  attention : String := "Attention.lean: φ allocation across modes"
  /-- B -/
  binding : String := "Binding.lean: Unity via Θ-coupling (GCIC)"
  binding_problem : String := "Binding.lean: How features unify into objects"
  bodily_self : String := "Self.lean: Body ownership (Mode 4 + Mode 1)"
  /-- C -/
  c_threshold : String := "Core.lean: Recognition cost C≥1 for actualization"
  calculus : String := "Calculus.lean: Formal algebra for qualia operations"
  category_theory : String := "CategoryTheory.lean: Categorical structure of qualia"
  chromesthesia : String := "Synesthesia.lean: Sound → color synesthesia"
  chronic_pain : String := "Pain.lean: Persistent pain syndromes"
  circumplex : String := "Emotions.lean: Valence × Arousal model"
  clinical : String := "Clinical.lean: Treatment models based on ULQ"
  cognitive : String := "Thought.lean: Inner speech, imagery, meta-cognition"
  comparative : String := "Comparative.lean: Cross-species qualia analysis"
  computation : String := "Computation.lean: Information processing in experience"
  consciousness : String := "Experience.lean: C≥1 state with unified qualia"
  /-- D -/
  death : String := "Death.lean: Cessation of Θ-binding and qualia"
  depersonalization : String := "Self.lean: Mode 4 disconnected from Mode 1"
  developmental : String := "Developmental.lean: Lifespan qualia development"
  dreams : String := "Dreams.lean: C<1 states with relaxed mode coherence"
  dynamics : String := "Dynamics.lean: Temporal evolution of qualia"
  /-- E -/
  ego_death : String := "Self.lean: Mode 4 → 0, Θ expands"
  emotions : String := "Emotions.lean: Emotional qualia taxonomy"
  entropy : String := "Thermodynamics.lean: Disorder in qualia space"
  ethics : String := "Ethics.lean: Virtue-qualia connection (blocked)"
  evolution : String := "Evolution.lean: Why qualia evolved"

/-- Index A-E -/
def indexAE : IndexAE := {}

/-! ## Alphabetical Index F-M -/

/-- Concepts F-M -/
structure IndexFM where
  /-- F -/
  free_energy : String := "Thermodynamics.lean: J-cost minimization"
  free_will : String := "Agency.lean: Compatibilist with quantum element"
  /-- G -/
  geometry : String := "Geometry.lean: Geometric structure of qualia space"
  golden_ratio : String := "Core.lean: φ in intensity levels, aesthetics"
  /-- H -/
  hard_problem : String := "Philosophy.lean: Dissolved by RS derivation"
  hedonic_valence : String := "Core.lean: Pleasure/pain from σ-gradient"
  hypnagogia : String := "Dreams.lean: N1 sleep entry state"
  /-- I -/
  illusions : String := "Perception.lean: Reveal constructive nature"
  imagery : String := "Thought.lean: Mental pictures (visual, auditory)"
  inattentional_blindness : String := "Attention.lean: φ≈0 misses stimulus"
  inner_speech : String := "Thought.lean: Verbal thinking (Mode 2)"
  intensity : String := "Core.lean: φ-level determines intensity"
  interoception : String := "Perception.lean: Internal body states"
  /-- J -/
  jhana : String := "Meditation.lean: Absorption states (1st-8th)"
  /-- L -/
  language : String := "Language.lean: Qualia-linguistic mapping"
  libet : String := "Agency.lean: Readiness potential experiment"
  logic : String := "Logic.lean: Formal logic of qualia propositions"
  lucid_dreaming : String := "Dreams.lean: Metacognition in dreams"
  /-- M -/
  meditation : String := "Meditation.lean: Contemplative practices"
  memory : String := "Memory.lean: Memory traces and qualia"
  meta_cognition : String := "Thought.lean: Thinking about thinking (Mode 4)"
  mind_wandering : String := "Thought.lean: Spontaneous thought (~50% of time)"
  mirror_touch : String := "Synesthesia.lean: Seeing → feeling touch"
  mode : String := "Core.lean: DFT mode k determines qualitative character"
  mood : String := "Emotions.lean: Background qualia state"
  moral_responsibility : String := "Agency.lean: Tracks Mode 4 involvement"

/-- Index F-M -/
def indexFM : IndexFM := {}

/-! ## Alphabetical Index N-Z -/

/-- Concepts N-Z -/
structure IndexNZ where
  /-- N -/
  narrative_self : String := "Self.lean: Life story (Mode 4 + Mode 2)"
  nde : String := "Death.lean: Near-death experience"
  nirvana : String := "Meditation.lean: Permanent σ=0"
  no_self : String := "Self.lean: Buddhist anatta compatible with ULQ"
  /-- P -/
  pain : String := "Pain.lean: Negative valence qualia"
  pathology : String := "Pathology.lean: Psychiatric conditions as qualia disruption"
  perception : String := "Perception.lean: Perceptual qualia and illusions"
  personal_identity : String := "Self.lean: Self as process, not substance"
  phenomenal_time : String := "PhenomenalTime.lean: Subjective duration"
  philosophy : String := "Philosophy.lean: Philosophy of mind connections"
  predictions : String := "Predictions.lean: Testable empirical predictions"
  /-- Q -/
  qualia_space : String := "Core.lean: Mode × Intensity × Valence × Temporal"
  qtoken : String := "Core.lean: WToken with experiential fiber"
  quantum : String := "Quantum.lean: Quantum aspects of consciousness"
  /-- R -/
  reappraisal : String := "Emotions.lean: Mode 4 changes interpretation"
  rem_sleep : String := "Dreams.lean: Rapid eye movement stage"
  /-- S -/
  self : String := "Self.lean: Self-awareness and identity"
  sigma : String := "Core.lean: σ-gradient determines valence"
  social : String := "Social.lean: Intersubjective qualia"
  stream : String := "Thought.lean: Stream of consciousness"
  sublime : String := "Aesthetics.lean: High intensity, mixed valence"
  summary : String := "Summary.lean: Complete theory overview"
  synesthesia : String := "Synesthesia.lean: Cross-modal Θ-binding"
  /-- T -/
  tau : String := "Core.lean: τ-offset determines temporal quality"
  taxonomy : String := "Taxonomy.lean: Detailed qualia taxonomy"
  terminal_lucidity : String := "Death.lean: Clarity before death"
  theta : String := "Binding.lean: Global phase Θ for binding"
  thermodynamics : String := "Thermodynamics.lean: Entropy and free energy"
  thought : String := "Thought.lean: Cognitive qualia"
  topology : String := "Topology.lean: Topological structure"
  twenty_types : String := "Classification.lean: 20 canonical qualia types"
  /-- U-Z -/
  umwelt : String := "Comparative.lean: Species-specific perceptual world"
  unsymbolized : String := "Thought.lean: Knowing without words/images"
  wtoken : String := "Core.lean: Base semantic atom from ULL"
  zombies : String := "Philosophy.lean: Impossible (τ≠0 necessitates qualia)"

/-- Index N-Z -/
def indexNZ : IndexNZ := {}

/-! ## Category Index -/

/-- Concepts by category -/
structure CategoryIndex where
  /-- Structures -/
  structures : List String := ["QualiaMode", "IntensityLevel", "HedonicValence",
                               "TemporalQuality", "QualiaSpace", "QToken"]
  /-- Mechanisms -/
  mechanisms : List String := ["C≥1 threshold", "Θ-binding", "σ-gradient",
                               "Mode activation", "φ-allocation"]
  /-- Phenomena -/
  phenomena : List String := ["Perception", "Attention", "Memory", "Emotion",
                              "Thought", "Dreams", "Pain", "Synesthesia"]
  /-- States -/
  states : List String := ["Consciousness", "Meditation", "Altered states",
                           "Sleep stages", "Flow", "Ego death"]
  /-- Disorders -/
  disorders : List String := ["ADHD", "Depression", "Anxiety", "Schizophrenia",
                              "Dissociation", "Pain syndromes"]
  /-- Philosophy -/
  philosophy : List String := ["Hard problem", "Binding problem", "Free will",
                               "Personal identity", "Zombies", "Afterlife"]

/-- Category index -/
def categoryIndex : CategoryIndex := {}

/-! ## Status Report -/

def index_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ CONCEPT INDEX                                  ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  ALPHABETICAL: A-E, F-M, N-Z sections                        ║\n" ++
  "║  BY CATEGORY:                                                ║\n" ++
  "║  • Structures: QualiaMode, IntensityLevel, etc.              ║\n" ++
  "║  • Mechanisms: C≥1, Θ-binding, σ-gradient                    ║\n" ++
  "║  • Phenomena: Perception, Emotion, Dreams                    ║\n" ++
  "║  • States: Consciousness, Meditation, Sleep                  ║\n" ++
  "║  • Disorders: ADHD, Depression, Pain                         ║\n" ++
  "║  • Philosophy: Hard problem, Free will, Identity             ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  CROSS-REFERENCES: Each entry points to source module        ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check index_status

end IndisputableMonolith.ULQ.Index
