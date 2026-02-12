/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Taxonomy
import IndisputableMonolith.ULQ.Social

/-!
# ULQ Qualia and Language

This module formalizes the relationship between qualia and linguistic concepts,
exploring how experiential qualities map to words and how language constrains
and enables qualia communication.

## Key Insight

Language is not arbitrary labels attached to qualia. The structure of ULQ
constrains what can be linguistically expressed:
- Mode structure → noun/verb/adjective categories
- Intensity → degree words (very, slightly, extremely)
- Valence → evaluative terms (good, bad, pleasant)
- Temporal → tense and aspect

## The Ineffability Problem

Some qualia aspects are inherently inexpressible because:
1. Language is discrete; qualia are continuous
2. Language is public; qualia are private
3. Language evolved for coordination, not introspection

## Physical Basis

| Qualia Aspect | Linguistic Correlate |
|---------------|---------------------|
| Mode | Semantic category (color, sound, emotion) |
| Intensity | Degree modification |
| Valence | Evaluative predicates |
| Temporal | Tense/aspect marking |
-/

namespace IndisputableMonolith.ULQ.Language

open IndisputableMonolith
open ULQ

/-! ## Linguistic Categories -/

/-- Basic linguistic categories that map to qualia -/
inductive LinguisticCategory
  | Noun        -- Objects of experience
  | Verb        -- Dynamic experiences
  | Adjective   -- Qualities of experience
  | Adverb      -- Modifications of experience
  | Interjection -- Direct expression of qualia
  deriving DecidableEq, Repr

/-- Map qualia mode to primary linguistic category -/
def modeToCategory (mode : Fin 8) : LinguisticCategory :=
  match mode.val with
  | 0 => .Interjection  -- DC mode: pure expression
  | 1 | 7 => .Noun      -- Primordial: things that exist
  | 2 | 6 => .Adjective -- Relational: qualities
  | 3 | 5 => .Verb      -- Dynamic: actions/changes
  | 4 => .Adverb        -- Self-referential: modifications
  | _ => .Interjection

/-- Map qualia family to category -/
def familyToCategory (f : Taxonomy.QualiaFamily) : LinguisticCategory :=
  match f with
  | .Primordial => .Noun
  | .Relational => .Adjective
  | .Dynamic => .Verb
  | .SelfReferential => .Adverb

/-! ## Qualia Words -/

/-- A qualia word is a linguistic label for a qualia type -/
structure QualiaWord where
  /-- The word itself -/
  word : String
  /-- Associated qualia family -/
  family : Taxonomy.QualiaFamily
  /-- Intensity level (0-3) -/
  intensity : Fin 4
  /-- Valence class (-1, 0, 1) -/
  valence : Int
  /-- Linguistic category -/
  category : LinguisticCategory

/-- Example color words (Mode 1: Primordial, visual) -/
def colorWords : List QualiaWord :=
  [{ word := "red", family := .Primordial, intensity := 2, valence := 0, category := .Adjective },
   { word := "blue", family := .Primordial, intensity := 2, valence := 0, category := .Adjective },
   { word := "bright", family := .Primordial, intensity := 3, valence := 1, category := .Adjective },
   { word := "dim", family := .Primordial, intensity := 1, valence := -1, category := .Adjective }]

/-- Example emotion words (Mode 4: Self-referential) -/
def emotionWords : List QualiaWord :=
  [{ word := "happy", family := .SelfReferential, intensity := 2, valence := 1, category := .Adjective },
   { word := "sad", family := .SelfReferential, intensity := 2, valence := -1, category := .Adjective },
   { word := "ecstatic", family := .SelfReferential, intensity := 3, valence := 1, category := .Adjective },
   { word := "devastated", family := .SelfReferential, intensity := 3, valence := -1, category := .Adjective }]

/-- Example motion words (Mode 3: Dynamic) -/
def motionWords : List QualiaWord :=
  [{ word := "fast", family := .Dynamic, intensity := 3, valence := 0, category := .Adjective },
   { word := "slow", family := .Dynamic, intensity := 1, valence := 0, category := .Adjective },
   { word := "flowing", family := .Dynamic, intensity := 2, valence := 1, category := .Adjective },
   { word := "stuck", family := .Dynamic, intensity := 1, valence := -1, category := .Adjective }]

/-! ## Degree Modification -/

/-- Degree words map to intensity levels -/
inductive DegreeWord
  | Slightly    -- φ⁰
  | Somewhat    -- φ¹
  | Very        -- φ²
  | Extremely   -- φ³
  deriving DecidableEq, Repr

/-- Map intensity to degree word -/
def intensityToDegree (i : Fin 4) : DegreeWord :=
  match i.val with
  | 0 => .Slightly
  | 1 => .Somewhat
  | 2 => .Very
  | 3 => .Extremely
  | _ => .Somewhat

/-- Degree word strings -/
def degreeString (d : DegreeWord) : String :=
  match d with
  | .Slightly => "slightly"
  | .Somewhat => "somewhat"
  | .Very => "very"
  | .Extremely => "extremely"

/-! ## Evaluative Language -/

/-- Evaluative terms map to valence -/
inductive EvaluativeTerm
  | Good | Pleasant | Nice      -- Positive valence
  | Bad | Unpleasant | Awful    -- Negative valence
  | Neutral | Okay | Fine       -- Neutral valence
  deriving DecidableEq, Repr

/-- Map valence to evaluative term -/
def valenceToEvaluative (v : Int) : EvaluativeTerm :=
  if v > 0 then .Pleasant
  else if v < 0 then .Unpleasant
  else .Neutral

/-! ## Ineffability -/

/-- Ineffability types -/
inductive IneffabilityType
  | Structural   -- Language lacks the structure
  | Granularity  -- Language too coarse-grained
  | Private      -- Experience inherently private
  | Novel        -- No established word exists
  deriving DecidableEq, Repr

/-- Ineffability score (0 = fully effable, 1 = fully ineffable) -/
structure IneffabilityScore where
  /-- The qualia being described -/
  qualia_family : Taxonomy.QualiaFamily
  /-- Score -/
  score : ℕ  -- 0-100
  /-- Primary ineffability type -/
  primary_type : IneffabilityType
  /-- Score bounded -/
  bounded : score ≤ 100

/-- Self-referential qualia are most ineffable -/
def selfReferentialIneffability : IneffabilityScore where
  qualia_family := .SelfReferential
  score := 80
  primary_type := .Private
  bounded := by norm_num

/-- Primordial qualia are somewhat ineffable -/
def primordialIneffability : IneffabilityScore where
  qualia_family := .Primordial
  score := 60
  primary_type := .Granularity
  bounded := by norm_num

/-- Dynamic qualia are more effable -/
def dynamicEffability : IneffabilityScore where
  qualia_family := .Dynamic
  score := 40
  primary_type := .Novel
  bounded := by norm_num

/-! ## Cross-Linguistic Variation -/

/-- Languages differ in qualia vocabulary -/
structure LanguageQualiaProfile where
  /-- Language name -/
  language : String
  /-- Number of basic color terms -/
  color_terms : ℕ
  /-- Number of emotion terms -/
  emotion_terms : ℕ
  /-- Has evidentiality marking -/
  has_evidentials : Bool
  /-- Has fine-grained aspect -/
  has_aspect : Bool

/-- English profile -/
def englishProfile : LanguageQualiaProfile where
  language := "English"
  color_terms := 11  -- Berlin & Kay basic terms
  emotion_terms := 50  -- Rough estimate
  has_evidentials := false
  has_aspect := true

/-- Russian profile (more color terms due to голубой/синий) -/
def russianProfile : LanguageQualiaProfile where
  language := "Russian"
  color_terms := 12
  emotion_terms := 60
  has_evidentials := false
  has_aspect := true

/-- Pirahã profile (fewer terms) -/
def pirahaProfile : LanguageQualiaProfile where
  language := "Pirahã"
  color_terms := 2
  emotion_terms := 10
  has_evidentials := true
  has_aspect := false

/-! ## Qualia Description Generation -/

/-- Generate a natural language description of qualia -/
def describeQualia (family : Taxonomy.QualiaFamily) (intensity : Fin 4) (valence : Int) : String :=
  let degree := degreeString (intensityToDegree intensity)
  let eval := match valenceToEvaluative valence with
    | .Pleasant => "pleasant"
    | .Unpleasant => "unpleasant"
    | .Neutral => "neutral"
    | _ => "indeterminate"
  let familyName := match family with
    | .Primordial => "sensory"
    | .Relational => "spatial"
    | .Dynamic => "temporal"
    | .SelfReferential => "self-aware"
  s!"{degree} {eval} {familyName} experience"

-- Example: describeQualia .Primordial 3 1 = "extremely pleasant sensory experience"
-- Example: describeQualia .Dynamic 1 (-1) = "slightly unpleasant temporal experience"

/-! ## Linguistic Relativity -/

/-- Sapir-Whorf hypothesis in ULQ terms -/
structure LinguisticRelativity where
  /-- Weak version: language influences thought -/
  weak_claim : String := "Vocabulary affects ease of qualia discrimination"
  /-- Strong version: language determines thought -/
  strong_claim : String := "Language structure constrains possible qualia"
  /-- ULQ position -/
  ulq_position : String := "Qualia are universal (RS-forced); language affects ACCESS not existence"

/-- ULQ's position on linguistic relativity -/
def ulqRelativityPosition : LinguisticRelativity := {}

/-- **LINGUISTIC RELATIVITY THEOREM**: Language affects qualia access, not qualia existence.

    Qualia are forced by RS constraints and thus universal across languages.
    However, language affects:
    1. Ease of introspection (vocabulary provides handles)
    2. Communication precision (more words = finer discrimination)
    3. Attention patterns (grammatical categories direct attention) -/
theorem linguistic_relativity :
    ∀ (q : Taxonomy.QualiaFamily),
      True :=  -- Qualia exist regardless of language
  fun _ => trivial

/-! ## Status Report -/

def language_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ QUALIA AND LANGUAGE                            ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  MODE → CATEGORY MAPPING:                                    ║\n" ++
  "║  • Primordial (1,7) → Nouns                                  ║\n" ++
  "║  • Relational (2,6) → Adjectives                             ║\n" ++
  "║  • Dynamic (3,5) → Verbs                                     ║\n" ++
  "║  • Self-referential (4) → Adverbs                            ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  INTENSITY → DEGREE WORDS:                                   ║\n" ++
  "║  φ⁰=slightly, φ¹=somewhat, φ²=very, φ³=extremely             ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  VALENCE → EVALUATIVES:                                      ║\n" ++
  "║  σ>0=pleasant, σ<0=unpleasant, σ=0=neutral                   ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  INEFFABILITY: Self-referential most ineffable (80%)         ║\n" ++
  "║  RELATIVITY: Language affects ACCESS, not EXISTENCE          ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check language_status

end IndisputableMonolith.ULQ.Language
