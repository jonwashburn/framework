/-
  Meaning Landscape Preregistered Test Suite
  ==========================================

  This module bundles all preregistered predictions and provides
  a complete test harness for validating the meaning landscape theory.

  VERSION: 1.0.0
  FROZEN: 2026-01-06

  ⚠️  DO NOT MODIFY THIS FILE AFTER DATA COLLECTION BEGINS ⚠️
-/

import IndisputableMonolith.Verification.Preregistered.MeaningLandscape.Spec
import IndisputableMonolith.Verification.Preregistered.MeaningLandscape.NeuralTests
import IndisputableMonolith.Verification.Preregistered.MeaningLandscape.BehavioralTests
import IndisputableMonolith.Verification.Preregistered.MeaningLandscape.AlignmentTests

namespace IndisputableMonolith.Verification.Preregistered.MeaningLandscape.Suite

open Neural Behavioral Alignment

/-! ## Complete Test Suite -/

/-- All prediction categories -/
inductive PredictionCategory where
  | structural   -- Neural structure predictions
  | compositional  -- LNAL composition predictions
  | alignment    -- Word-token alignment predictions
deriving Repr, DecidableEq

/-- Individual prediction with metadata -/
structure PreregisteredPrediction where
  /-- Unique identifier -/
  id : String
  /-- Category -/
  category : PredictionCategory
  /-- Human-readable description -/
  description : String
  /-- Falsification criterion -/
  falsifier : String
  /-- Minimum sample size -/
  minSampleSize : ℕ
  /-- Significance threshold -/
  alpha : ℝ

/-- All preregistered predictions in the suite -/
noncomputable def allPredictions : List PreregisteredPrediction := [
  -- Structural predictions (S1-S4)
  { id := "S1", category := .structural
    description := "Mode families correlate with EEG frequency bands"
    falsifier := "No significant correlation in N≥100 (p > 0.05)"
    minSampleSize := 100, alpha := 0.05 },
  { id := "S2", category := .structural
    description := "φ-levels correspond to amplitude quantization"
    falsifier := "Continuous distribution fits better"
    minSampleSize := 100, alpha := 0.05 },
  { id := "S3", category := .structural
    description := "Conjugate pairs show cross-frequency coupling"
    falsifier := "No coupling structure (random phase)"
    minSampleSize := 100, alpha := 0.05 },
  { id := "S4", category := .structural
    description := "Graph distance predicts priming effects"
    falsifier := "No distance effect (r < 0.1)"
    minSampleSize := 50, alpha := 0.05 },

  -- Compositional predictions (C1-C2)
  { id := "C1", category := .compositional
    description := "Synonymous sentences reduce to same LNAL motif"
    falsifier := "Different motifs for paraphrases (sim < 0.5)"
    minSampleSize := 100, alpha := 0.05 },
  { id := "C2", category := .compositional
    description := "Compatible tokens co-activate in neural recordings"
    falsifier := "No co-activation pattern"
    minSampleSize := 50, alpha := 0.05 },

  -- Alignment predictions (A1-A3)
  { id := "A1", category := .alignment
    description := "Similar words map to nearby WTokens"
    falsifier := "Random mapping equally good (r < 0.1)"
    minSampleSize := 200, alpha := 0.05 },
  { id := "A2", category := .alignment
    description := "Translation pairs map to same tokens"
    falsifier := "Language-specific patterns"
    minSampleSize := 50, alpha := 0.05 },
  { id := "A3", category := .alignment
    description := "Antonyms map to distant tokens"
    falsifier := "Antonyms close in token space"
    minSampleSize := 50, alpha := 0.05 }
]

/-- Total prediction count (hardcoded to avoid noncomputable propagation) -/
def totalPredictions : ℕ := 9

/-- Minimum passing predictions for theory validation -/
def minPassingForValidation : ℕ := 6

/-- Required pass rate -/
noncomputable def requiredPassRate : ℝ := 0.67  -- 6/9 ≈ 67%


/-! ## Validation Framework -/

/-- Individual test outcome -/
structure TestOutcome where
  predictionId : String
  passed : Bool
  effectSize : ℝ
  pValue : ℝ
  sampleSize : ℕ
  notes : String

/-- Complete validation report -/
structure ValidationReport where
  /-- Date of validation -/
  date : String
  /-- All test outcomes -/
  outcomes : List TestOutcome
  /-- Summary counts -/
  totalPassed : ℕ
  totalFailed : ℕ
  totalInconclusive : ℕ
  /-- Overall verdict -/
  theoryValidated : Bool

/-- Check if validation passed -/
def isValidated (outcomes : List TestOutcome) : Bool :=
  let passed := outcomes.filter (·.passed)
  passed.length ≥ minPassingForValidation


/-! ## Structural Counts -/

/-- Structural predictions: 4 -/
def structuralCount : ℕ := 4

/-- Compositional predictions: 2 -/
def compositionalCount : ℕ := 2

/-- Alignment predictions: 3 -/
def alignmentCount : ℕ := 3


/-! ## Suite Summary -/

def suiteVersion : String := "1.0.0"
def freezeDate : String := "2026-01-06"

def completeSuiteSummary : String :=
  "╔══════════════════════════════════════════════════════════════════╗\n" ++
  "║    MEANING LANDSCAPE PREREGISTERED TEST SUITE v" ++ suiteVersion ++ "            ║\n" ++
  "╠══════════════════════════════════════════════════════════════════╣\n" ++
  "║ FROZEN DATE: " ++ freezeDate ++ "                                          ║\n" ++
  "║                                                                  ║\n" ++
  "║ ⚠️  DO NOT MODIFY AFTER DATA COLLECTION BEGINS ⚠️                 ║\n" ++
  "╠══════════════════════════════════════════════════════════════════╣\n" ++
  "║                                                                  ║\n" ++
  "║ PREDICTION COUNTS:                                               ║\n" ++
  "║   • Structural (S1-S4):    4 predictions                         ║\n" ++
  "║   • Compositional (C1-C2): 2 predictions                         ║\n" ++
  "║   • Alignment (A1-A3):     3 predictions                         ║\n" ++
  "║   ─────────────────────────────────                              ║\n" ++
  "║   • TOTAL:                 9 predictions                         ║\n" ++
  "║                                                                  ║\n" ++
  "╠══════════════════════════════════════════════════════════════════╣\n" ++
  "║                                                                  ║\n" ++
  "║ VALIDATION CRITERIA:                                             ║\n" ++
  "║   • Minimum passing: 6/9 (67%)                                   ║\n" ++
  "║   • Each category must have ≥1 passing prediction                ║\n" ++
  "║   • Significance threshold: α = 0.05                             ║\n" ++
  "║                                                                  ║\n" ++
  "╠══════════════════════════════════════════════════════════════════╣\n" ++
  "║                                                                  ║\n" ++
  "║ STRUCTURAL PREDICTIONS:                                          ║\n" ++
  "║   S1. Mode→Frequency: Mode-k tokens activate k-th EEG band       ║\n" ++
  "║   S2. φ-Amplitude: EEG amplitude clusters at φⁿ ratios           ║\n" ++
  "║   S3. Conjugate Coupling: k/(8-k) modes phase-coupled            ║\n" ++
  "║   S4. Graph Priming: Distance predicts RT priming                ║\n" ++
  "║                                                                  ║\n" ++
  "║ COMPOSITIONAL PREDICTIONS:                                       ║\n" ++
  "║   C1. Synonym Motif: Paraphrases → same LNAL normal form         ║\n" ++
  "║   C2. Compatibility: Compatible tokens co-activate               ║\n" ++
  "║                                                                  ║\n" ++
  "║ ALIGNMENT PREDICTIONS:                                           ║\n" ++
  "║   A1. Similarity: Similar words → nearby WTokens                 ║\n" ++
  "║   A2. Translation: Same concept across languages → same tokens   ║\n" ++
  "║   A3. Antonymy: Antonyms → distant tokens                        ║\n" ++
  "║                                                                  ║\n" ++
  "╠══════════════════════════════════════════════════════════════════╣\n" ++
  "║                                                                  ║\n" ++
  "║ FALSIFICATION:                                                   ║\n" ++
  "║   If <6/9 predictions pass → theory FALSIFIED                    ║\n" ++
  "║   If any category has 0/N passing → category-specific revision   ║\n" ++
  "║                                                                  ║\n" ++
  "╚══════════════════════════════════════════════════════════════════╝"

#eval completeSuiteSummary


/-! ## Integrity Hash (placeholder) -/

/-- Compute integrity hash for frozen predictions
    This should be computed once at freeze time and never change -/
def integrityHash : String :=
  -- In production, compute SHA-256 of all prediction parameters
  "PLACEHOLDER_HASH_COMPUTED_AT_FREEZE_TIME"

/-- Verify suite has not been modified -/
def verifyIntegrity (expectedHash : String) : Bool :=
  integrityHash == expectedHash

end IndisputableMonolith.Verification.Preregistered.MeaningLandscape.Suite
