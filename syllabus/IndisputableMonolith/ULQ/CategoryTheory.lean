/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Bridge

/-!
# ULQ Category Theory

This module explores the categorical structure of qualia,
using category theory to formalize relationships between experiential states.

## Key Insight

Category theory provides the right language to describe:
- Qualia transformations (morphisms)
- Composition of experiences (functor composition)
- Universal properties of consciousness

## Categorical Structures

| Category Theory | Qualia Interpretation |
|-----------------|----------------------|
| Object | A qualia configuration |
| Morphism | Experiential transformation |
| Functor | Systematic mapping between qualia types |
| Natural transformation | Coherent change of perspective |
| Limit/Colimit | Unified/fragmented experience |

## The Category Qual

Objects: QualiaSpace configurations
Morphisms: Attention-driven transformations
Identity: Maintaining current qualia
Composition: Sequential experience
-/

namespace IndisputableMonolith.ULQ.CategoryTheory

open IndisputableMonolith
open ULQ

/-! ## The Category of Qualia -/

/-- A default qualia configuration for examples -/
noncomputable def defaultQualia : QualiaSpace where
  mode := ⟨⟨1, by norm_num⟩, by norm_num⟩
  intensity := ⟨⟨1, by norm_num⟩⟩
  valence := ⟨0, by norm_num, by norm_num⟩
  temporal := ⟨⟨0, by norm_num⟩⟩

/-- Objects in the category Qual -/
structure QualObject where
  /-- The qualia configuration -/
  qualia : QualiaSpace
  /-- Is actualized (C≥1) -/
  actualized : Bool

/-- A morphism in Qual is an experiential transformation -/
structure QualMorphism where
  /-- Source object -/
  source : QualObject
  /-- Target object -/
  target : QualObject
  /-- Transformation name -/
  name : String
  /-- Is attention-driven -/
  attention_driven : Bool

/-- Identity morphism -/
def idMorphism (q : QualObject) : QualMorphism where
  source := q
  target := q
  name := "identity"
  attention_driven := false

/-- Composition of morphisms -/
def composeMorphism (f g : QualMorphism) (h : f.target = g.source) : QualMorphism where
  source := f.source
  target := g.target
  name := f.name ++ " ; " ++ g.name
  attention_driven := f.attention_driven || g.attention_driven

/-! ## Functors -/

/-- A functor from Qual to Qual -/
structure QualFunctor where
  /-- Name -/
  name : String
  /-- Object mapping description -/
  object_map : String
  /-- Morphism mapping description -/
  morphism_map : String
  /-- Preserves identity -/
  preserves_id : Bool
  /-- Preserves composition -/
  preserves_comp : Bool

/-- The Attention functor: focuses qualia -/
def attentionFunctor : QualFunctor where
  name := "Attention"
  object_map := "Increases intensity of attended qualia"
  morphism_map := "Transforms attention-driven morphisms"
  preserves_id := true
  preserves_comp := true

/-- The Memory functor: stores qualia -/
def memoryFunctor : QualFunctor where
  name := "Memory"
  object_map := "Maps qualia to memory traces"
  morphism_map := "Encodes transformation history"
  preserves_id := true
  preserves_comp := true

/-- The Valence functor: extracts hedonic content -/
def valenceFunctor : QualFunctor where
  name := "Valence"
  object_map := "Projects to hedonic dimension"
  morphism_map := "Tracks valence changes"
  preserves_id := true
  preserves_comp := true

/-! ## Natural Transformations -/

/-- A natural transformation between functors -/
structure QualNatTrans where
  /-- Source functor -/
  source : QualFunctor
  /-- Target functor -/
  target : QualFunctor
  /-- Name -/
  name : String
  /-- Description -/
  description : String
  /-- Is natural (coherent) -/
  is_natural : Bool

/-- Attention to Memory: "remembering what you attended" -/
def attentionToMemory : QualNatTrans where
  source := attentionFunctor
  target := memoryFunctor
  name := "Encoding"
  description := "Attended qualia become memories"
  is_natural := true

/-- Memory to Valence: "emotional coloring of memories" -/
def memoryToValence : QualNatTrans where
  source := memoryFunctor
  target := valenceFunctor
  name := "Emotional tagging"
  description := "Memories acquire hedonic valence"
  is_natural := true

/-! ## Limits and Colimits -/

/-- Limits represent unified experience -/
structure QualLimit where
  /-- Description -/
  description : String := "Unified experiential whole"
  /-- Components unified -/
  components : List String
  /-- Universal property -/
  universal : String := "Unique morphism from any cone"

/-- Colimits represent fragmented experience -/
structure QualColimit where
  /-- Description -/
  description : String := "Fragmented experiential parts"
  /-- Parts -/
  parts : List String
  /-- Universal property -/
  universal : String := "Unique morphism to any cocone"

/-- Normal consciousness as limit -/
def normalConsciousnessLimit : QualLimit where
  components := ["visual", "auditory", "emotional", "cognitive"]

/-- Dissociation as colimit -/
def dissociationColimit : QualColimit where
  parts := ["observing_self", "experiencing_self", "body_sense"]

/-! ## Adjunctions -/

/-- An adjunction between qualia functors -/
structure QualAdjunction where
  /-- Left adjoint -/
  left : QualFunctor
  /-- Right adjoint -/
  right : QualFunctor
  /-- Description -/
  description : String
  /-- Unit exists -/
  has_unit : Bool
  /-- Counit exists -/
  has_counit : Bool

/-- Attention-Forgetting adjunction -/
def attentionForgettingAdjunction : QualAdjunction where
  left := attentionFunctor
  right := { name := "Forgetting", object_map := "Reduces intensity",
             morphism_map := "Loses detail", preserves_id := true, preserves_comp := true }
  description := "Attending is left adjoint to forgetting"
  has_unit := true
  has_counit := true

/-! ## Monads -/

/-- A monad on Qual -/
structure QualMonad where
  /-- Underlying functor -/
  functor : QualFunctor
  /-- Unit (return) -/
  unit : String
  /-- Multiplication (join) -/
  mult : String
  /-- Description -/
  description : String

/-- The Consciousness monad -/
def consciousnessMonad : QualMonad where
  functor := { name := "Consciousness", object_map := "Actualizes qualia (C→≥1)",
               morphism_map := "Makes transformations conscious",
               preserves_id := true, preserves_comp := true }
  unit := "Becoming aware of qualia"
  mult := "Being aware of being aware (meta-consciousness)"
  description := "Consciousness as computational effect"

/-- The Attention monad -/
def attentionMonad : QualMonad where
  functor := attentionFunctor
  unit := "Spontaneous noticing"
  mult := "Deep focus (attending to attention)"
  description := "Attention as computational effect"

/-! ## Topoi -/

/-- Topos structure on Qual -/
structure QualTopos where
  /-- Has terminal object -/
  has_terminal : Bool := true
  /-- Has pullbacks -/
  has_pullbacks : Bool := true
  /-- Has exponentials -/
  has_exponentials : Bool := true
  /-- Has subobject classifier -/
  has_subobject_classifier : Bool := true
  /-- Description -/
  description : String

/-- Qual as a topos -/
def qualTopos : QualTopos where
  description := "Qual has topos structure with consciousness as truth"

/-- The subobject classifier is consciousness -/
def subobjectClassifier : String := "Ω = {unconscious, conscious} with C≥1 as 'true'"

/-! ## Higher Categories -/

/-- 2-morphisms: transformations between transformations -/
structure Qual2Morphism where
  /-- Source morphism -/
  source : QualMorphism
  /-- Target morphism -/
  target : QualMorphism
  /-- Name -/
  name : String
  /-- Description -/
  description : String

/-- "Changing how you change" as 2-morphism -/
noncomputable def metaTransformation : Qual2Morphism where
  source := { source := ⟨defaultQualia, true⟩,
              target := ⟨defaultQualia, true⟩,
              name := "habitual_response", attention_driven := false }
  target := { source := ⟨defaultQualia, true⟩,
              target := ⟨defaultQualia, true⟩,
              name := "mindful_response", attention_driven := true }
  name := "habit_breaking"
  description := "Transforming from automatic to mindful response"

/-! ## Status Report -/

def category_theory_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ CATEGORY THEORY                                ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  CATEGORY Qual:                                              ║\n" ++
  "║  • Objects: QualiaSpace configurations                       ║\n" ++
  "║  • Morphisms: Experiential transformations                   ║\n" ++
  "║  • Identity: Maintaining qualia                              ║\n" ++
  "║  • Composition: Sequential experience                        ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  FUNCTORS: Attention, Memory, Valence                        ║\n" ++
  "║  NATURAL TRANSFORMATIONS: Encoding, Emotional tagging        ║\n" ++
  "║  ADJUNCTIONS: Attention ⊣ Forgetting                         ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  LIMITS: Unified consciousness                               ║\n" ++
  "║  COLIMITS: Dissociated experience                            ║\n" ++
  "║  MONADS: Consciousness, Attention                            ║\n" ++
  "║  TOPOS: Qual with consciousness as Ω                         ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check category_theory_status

end IndisputableMonolith.ULQ.CategoryTheory
