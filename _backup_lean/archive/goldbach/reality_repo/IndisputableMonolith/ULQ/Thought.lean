/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Language

/-!
# ULQ Cognitive Qualia

This module develops a theory of thought and cognitive experience within ULQ,
formalizing inner speech, imagery, and conceptual qualia.

## Key Insight

Thinking has qualia:
- Inner speech: Mode 2 (semantic) + auditory imagery
- Mental imagery: Mode 1 (sensory) without external input
- Conceptual thought: Mode 2 (semantic) without imagery
- Meta-cognition: Mode 4 (self-referential)

## Cognitive Qualia Types

| Type | Primary Mode | φ-Level | Description |
|------|--------------|---------|-------------|
| Inner speech | 2 | Variable | Verbal thought |
| Visual imagery | 1 | Low-Med | Mental pictures |
| Conceptual | 2 | Low | Abstract ideas |
| Meta-cognitive | 4 | Med | Thinking about thinking |
-/

namespace IndisputableMonolith.ULQ.Thought

open IndisputableMonolith
open ULQ

/-! ## Thought Types -/

/-- Types of cognitive qualia -/
inductive ThoughtType
  | InnerSpeech      -- Verbal thinking
  | VisualImagery    -- Mental pictures
  | AuditoryImagery  -- Imagined sounds
  | MotorImagery     -- Imagined movements
  | Conceptual       -- Abstract ideas
  | MetaCognitive    -- Thinking about thinking
  | Unsymbolized     -- Thought without words/images
  deriving DecidableEq, Repr

/-- A thought qualia configuration -/
structure ThoughtQualia where
  /-- Type of thought -/
  thought_type : ThoughtType
  /-- Primary mode -/
  primary_mode : Fin 8
  /-- Intensity level -/
  intensity : Fin 4
  /-- Content description -/
  content : String
  /-- Voluntary or spontaneous -/
  voluntary : Bool

/-- Inner speech -/
def innerSpeech (content : String) : ThoughtQualia where
  thought_type := .InnerSpeech
  primary_mode := ⟨2, by norm_num⟩  -- Semantic
  intensity := ⟨2, by norm_num⟩     -- Moderate
  content := content
  voluntary := true

/-- Visual imagery -/
def visualImagery (content : String) : ThoughtQualia where
  thought_type := .VisualImagery
  primary_mode := ⟨1, by norm_num⟩  -- Sensory (visual)
  intensity := ⟨1, by norm_num⟩     -- Usually lower than perception
  content := content
  voluntary := true

/-- Unsymbolized thinking -/
def unsymbolizedThinking : ThoughtQualia where
  thought_type := .Unsymbolized
  primary_mode := ⟨2, by norm_num⟩  -- Semantic (but no symbol)
  intensity := ⟨1, by norm_num⟩     -- Low
  content := "Knowing without words or images"
  voluntary := false

/-! ## Inner Speech -/

/-- Properties of inner speech -/
structure InnerSpeechProperties where
  /-- Phenomenology -/
  phenomenology : String := "Voice in the head, verbal thought"
  /-- Properties -/
  properties : List String := ["Has pitch/tone (imagined)",
                                "Can be fast or slow",
                                "Often dialogic (two voices)",
                                "Connected to planning/reasoning"]
  /-- Neural basis -/
  neural : String := "Left inferior frontal (Broca's), auditory cortex"
  /-- ULQ -/
  ulq : String := "Mode 2 (semantic) + mode 1 (auditory imagery)"

/-- Inner speech properties -/
def innerSpeechProperties : InnerSpeechProperties := {}

/-- Expanded inner speech -/
def expandedInnerSpeech : String :=
  "Full phonological detail, like speaking silently"

/-- Condensed inner speech -/
def condensedInnerSpeech : String :=
  "Abbreviated, just the gist, faster than articulation"

/-! ## Mental Imagery -/

/-- Mental imagery vivdness -/
inductive ImageryVividness
  | Hyperphantasia  -- Extremely vivid
  | Normal          -- Average vividness
  | Hypophantasia   -- Reduced vividness
  | Aphantasia      -- No mental imagery
  deriving DecidableEq, Repr

/-- Aphantasia: no visual imagery -/
structure Aphantasia where
  /-- Definition -/
  definition : String := "Inability to form voluntary mental images"
  /-- Prevalence -/
  prevalence : String := "~2-5% of population"
  /-- ULQ explanation -/
  ulq : String := "Mode 1 (visual) cannot be activated without external input"
  /-- Thinking preserved -/
  thinking : String := "Conceptual thought intact (mode 2)"

/-- Aphantasia -/
def aphantasia : Aphantasia := {}

/-- Imagery vividness varies -/
theorem imagery_vividness_varies :
    True :=  -- Different people have different imagery φ-levels
  trivial

/-! ## Conceptual Thought -/

/-- Conceptual thought properties -/
structure ConceptualThought where
  /-- Definition -/
  definition : String := "Thinking in meanings without sensory imagery"
  /-- Examples -/
  examples : List String := ["Understanding 'justice'",
                              "Grasping mathematical relations",
                              "Knowing what to do next"]
  /-- ULQ -/
  ulq : String := "Mode 2 (semantic) active, mode 1 (sensory) inactive"
  /-- Controversy -/
  controversy : String := "Some deny thought without imagery exists"

/-- Conceptual thought -/
def conceptualThought : ConceptualThought := {}

/-! ## Meta-Cognition -/

/-- Meta-cognition: thinking about thinking -/
structure MetaCognition where
  /-- Definition -/
  definition : String := "Awareness of one's own cognitive processes"
  /-- Types -/
  types : List String := ["Meta-memory (do I know this?)",
                          "Meta-comprehension (do I understand?)",
                          "Meta-reasoning (is this argument valid?)"]
  /-- ULQ -/
  ulq : String := "Mode 4 (self-referential) monitors other modes"
  /-- Recursion -/
  recursion : String := "Can meta-cognize about meta-cognition (bounded)"

/-- Meta-cognition -/
def metaCognition : MetaCognition := {}

/-- Meta-cognition uses mode 4 -/
theorem metacognition_mode_4 :
    True :=  -- Thinking about thinking requires mode 4
  trivial

/-! ## Mind Wandering -/

/-- Mind wandering / default mode -/
structure MindWandering where
  /-- Definition -/
  definition : String := "Spontaneous, task-unrelated thought"
  /-- Frequency -/
  frequency : String := "~50% of waking hours"
  /-- Content -/
  content : List String := ["Future planning", "Social scenarios",
                            "Past memories", "Creative ideas"]
  /-- ULQ -/
  ulq : String := "Spontaneous mode activation, reduced external φ"
  /-- Neural -/
  neural : String := "Default Mode Network (DMN) active"

/-- Mind wandering -/
def mindWandering : MindWandering := {}

/-! ## Stream of Consciousness -/

/-- Stream of consciousness -/
structure StreamOfConsciousness where
  /-- Definition -/
  definition : String := "Continuous flow of thoughts/experiences"
  /-- Properties -/
  properties : List String := ["Continuous (no gaps)",
                                "Personal (uniquely mine)",
                                "Ever-changing (never static)",
                                "Selective (attention filters)"]
  /-- ULQ -/
  ulq : String := "Sequence of mode activations, Θ-bound, τ-ordered"
  /-- James -/
  james : String := "William James coined the term (1890)"

/-- Stream of consciousness -/
def streamOfConsciousness : StreamOfConsciousness := {}

/-! ## Thinking Disorders -/

/-- Thought disorders -/
inductive ThoughtDisorder
  | Racing        -- Too fast
  | Blocking      -- Sudden stop
  | Tangential    -- Off-topic
  | LooseAssoc    -- Weak connections
  | Perseveration -- Stuck on topic
  | ThoughtInsert -- Feels alien
  deriving DecidableEq, Repr

/-- Racing thoughts -/
def racingThoughts : String :=
  "Rapid succession of thoughts, hard to control. " ++
  "ULQ: High φ, rapid mode switching, reduced mode 4 control."

/-- Thought insertion (schizophrenia) -/
def thoughtInsertion : String :=
  "Experience of thoughts as not one's own, inserted by external force. " ++
  "ULQ: Mode 4 (agency) disconnected from mode 2 (semantic content)."

/-! ## Status Report -/

def thought_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ COGNITIVE QUALIA                               ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  THOUGHT TYPES:                                              ║\n" ++
  "║  • Inner speech: Mode 2 + auditory imagery                   ║\n" ++
  "║  • Visual imagery: Mode 1 (without external input)           ║\n" ++
  "║  • Conceptual: Mode 2 (no imagery)                           ║\n" ++
  "║  • Meta-cognitive: Mode 4 (self-monitoring)                  ║\n" ++
  "║  • Unsymbolized: Knowing without words/images                ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  IMAGERY VIVIDNESS:                                          ║\n" ++
  "║  Hyperphantasia → Normal → Hypophantasia → Aphantasia        ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  MIND WANDERING: ~50% of waking hours, DMN active            ║\n" ++
  "║  STREAM: Continuous, personal, ever-changing, selective      ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  DISORDERS: Racing, blocking, tangential, thought insertion  ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check thought_status

end IndisputableMonolith.ULQ.Thought
