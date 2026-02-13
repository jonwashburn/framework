/-
  Meaning Landscape Preregistered Predictions
  ============================================

  This module contains FROZEN predictions that MUST NOT be modified
  after data collection begins. All predictions have explicit falsifier
  criteria that would invalidate the theory if violated.

  Version: 1.0.0
  Frozen Date: 2026-01-06
  Hash: [Computed at freeze time]
-/

import IndisputableMonolith.LightLanguage.MeaningLandscape.SemanticCoordinate
import IndisputableMonolith.LightLanguage.MeaningLandscape.MeaningGraph

namespace IndisputableMonolith.Verification.Preregistered.MeaningLandscape

open LightLanguage.MeaningLandscape

/-! ## Prediction Categories

We have three categories of falsifiable predictions:
1. **Structural Predictions**: Test that mode families, φ-levels, and conjugate pairs
   have neural correlates
2. **Compositional Predictions**: Test that LNAL reduction captures meaning
3. **Alignment Predictions**: Test that WToken space captures word meaning
-/

/-! ### 1. Structural Predictions -/

/-- Prediction S1: Mode families correlate with EEG frequency bands

    Mode-k tokens should preferentially activate in the k-th frequency band:
    - Mode 1: theta (4-8 Hz)
    - Mode 2: alpha (8-13 Hz)
    - Mode 3: beta (13-30 Hz)
    - Mode 4: gamma (30-100 Hz)

    Falsifier: No significant correlation in N≥100 subjects (p > 0.05) -/
structure PredictionS1_ModeFamilyNeural where
  /-- Minimum number of subjects -/
  minSubjects : ℕ := 100
  /-- Significance threshold (p-value) -/
  significanceThreshold : ℝ := 0.05
  /-- Expected frequency band for each mode (Hz) -/
  modeToBandLow : Fin 4 → ℝ := fun k =>
    match k with
    | ⟨0, _⟩ => 4    -- theta
    | ⟨1, _⟩ => 8    -- alpha
    | ⟨2, _⟩ => 13   -- beta
    | ⟨3, _⟩ => 30   -- gamma
  modeToBandHigh : Fin 4 → ℝ := fun k =>
    match k with
    | ⟨0, _⟩ => 8
    | ⟨1, _⟩ => 13
    | ⟨2, _⟩ => 30
    | ⟨3, _⟩ => 100

/-- Prediction S2: φ-levels correspond to amplitude quantization

    EEG amplitude during semantic processing should cluster at φ^n ratios:
    φ^0 = 1.0, φ^1 ≈ 1.618, φ^2 ≈ 2.618, φ^3 ≈ 4.236

    Falsifier: Continuous amplitude distribution (no clustering, p > 0.05) -/
structure PredictionS2_PhiLevelAmplitude where
  /-- Expected amplitude ratios -/
  phiLevels : Fin 4 → ℝ := fun k =>
    match k with
    | ⟨0, _⟩ => 1.0
    | ⟨1, _⟩ => 1.618
    | ⟨2, _⟩ => 2.618
    | ⟨3, _⟩ => 4.236
  /-- Tolerance for amplitude clustering -/
  clusterTolerance : ℝ := 0.15
  /-- Significance threshold -/
  significanceThreshold : ℝ := 0.05

/-- Prediction S3: Conjugate pairs show cross-frequency coupling

    Modes k and (8-k) should show phase-amplitude coupling:
    - Mode 1 (theta) couples with Mode 7 (gamma)
    - Mode 2 (alpha) couples with Mode 6 (high beta)
    - Mode 3 (beta) couples with Mode 5 (low gamma)

    Falsifier: No coupling structure (random phase relationships) -/
structure PredictionS3_ConjugateCoupling where
  /-- Conjugate mode pairs -/
  conjugatePairs : List (Fin 4 × Fin 4) := [(⟨0, by omega⟩, ⟨3, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩)]
  /-- Expected modulation index threshold -/
  modulationIndexThreshold : ℝ := 0.1
  /-- Significance threshold -/
  significanceThreshold : ℝ := 0.05

/-- Prediction S4: Semantic graph distance predicts priming effects

    Words mapping to nearby WTokens should show stronger priming effects
    (faster reaction times) than words mapping to distant tokens.

    Falsifier: No distance effect (r < 0.1 with distance) -/
structure PredictionS4_GraphPriming where
  /-- Minimum correlation coefficient -/
  minCorrelation : ℝ := 0.1
  /-- Number of word pairs to test -/
  minPairs : ℕ := 50
  /-- Significance threshold -/
  significanceThreshold : ℝ := 0.05


/-! ### 2. Compositional Predictions -/

/-- Prediction C1: Synonymous sentences reduce to same LNAL motif

    Two sentences with the same meaning should, after alignment and
    reduction to normal form, yield identical or highly similar motifs.

    Falsifier: Different motifs for paraphrases (similarity < 0.5) -/
structure PredictionC1_SynonymMotif where
  /-- Minimum similarity for synonymous sentences -/
  minSimilarity : ℝ := 0.5
  /-- Number of sentence pairs to test -/
  minPairs : ℕ := 100

/-- Prediction C2: Compatible tokens co-activate in neural recordings

    WTokens connected by "compatible" edges in the meaning graph
    should show elevated co-activation in fMRI/EEG during semantic tasks.

    Falsifier: No co-activation pattern (random activation) -/
structure PredictionC2_CompatibleCoactivation where
  /-- Expected co-activation elevation ratio -/
  coactivationRatio : ℝ := 1.5  -- 50% higher than baseline
  /-- Significance threshold -/
  significanceThreshold : ℝ := 0.05


/-! ### 3. Alignment Predictions -/

/-- Prediction A1: Similar words map to nearby WTokens

    Words with high semantic similarity (e.g., word2vec cosine > 0.7)
    should map to WTokens with low coordinate distance.

    Falsifier: Random mapping performs equally well (r < 0.1) -/
structure PredictionA1_WordSimilarity where
  /-- Minimum correlation between word similarity and token distance -/
  minCorrelation : ℝ := 0.1
  /-- Number of word pairs to test -/
  minPairs : ℕ := 200
  /-- Significance threshold -/
  significanceThreshold : ℝ := 0.05

/-- Prediction A2: Translation pairs map to same tokens

    The same concept expressed in different languages (English, Spanish,
    Chinese, etc.) should map to the same or highly similar WToken distribution.

    Falsifier: Language-specific patterns (significantly different tokens per language) -/
structure PredictionA2_TranslationConsistency where
  /-- Minimum alignment score for translation pairs -/
  minAlignmentScore : ℝ := 0.7
  /-- Number of translation pairs per language pair -/
  minPairsPerLanguage : ℕ := 50
  /-- Languages to test -/
  languages : List String := ["en", "es", "zh", "ar", "hi"]

/-- Prediction A3: Antonyms map to distant tokens

    Antonymous words should have large coordinate distance,
    specifically across φ-level or mode-family.

    Falsifier: Antonyms close in token space (distance < threshold) -/
structure PredictionA3_AntonymDistance where
  /-- Minimum distance for antonym pairs -/
  minDistance : ℝ := 0.5
  /-- Number of antonym pairs to test -/
  minPairs : ℕ := 50


/-! ## Frozen Prediction Instances -/

/-- The complete set of frozen predictions -/
structure FrozenPredictions where
  s1_modeFamilyNeural : PredictionS1_ModeFamilyNeural := {}
  s2_phiLevelAmplitude : PredictionS2_PhiLevelAmplitude := {}
  s3_conjugateCoupling : PredictionS3_ConjugateCoupling := {}
  s4_graphPriming : PredictionS4_GraphPriming := {}
  c1_synonymMotif : PredictionC1_SynonymMotif := {}
  c2_compatibleCoactivation : PredictionC2_CompatibleCoactivation := {}
  a1_wordSimilarity : PredictionA1_WordSimilarity := {}
  a2_translationConsistency : PredictionA2_TranslationConsistency := {}
  a3_antonymDistance : PredictionA3_AntonymDistance := {}

/-- Default frozen predictions instance -/
def frozenPredictions : FrozenPredictions := {}

/-- Total number of predictions -/
def predictionCount : ℕ := 9

/-- Minimum predictions that must pass for theory validation -/
def minPassingPredictions : ℕ := 6  -- 2/3 of predictions


/-! ## Validation Criteria -/

/-- Result of a single prediction test -/
inductive PredictionResult where
  | passed : ℝ → PredictionResult  -- effect size
  | failed : String → PredictionResult  -- failure reason
  | inconclusive : String → PredictionResult  -- insufficient data

/-- Overall validation result -/
structure ValidationResult where
  /-- Number of predictions passed -/
  passed : ℕ
  /-- Number of predictions failed -/
  failed : ℕ
  /-- Number of inconclusive results -/
  inconclusive : ℕ
  /-- Individual results -/
  results : List (String × PredictionResult)
  /-- Overall verdict -/
  isValid : Bool := passed ≥ minPassingPredictions

/-- Summary report for frozen predictions -/
def frozenPredictionsSummary : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║     MEANING LANDSCAPE PREREGISTERED PREDICTIONS v1.0        ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║ FROZEN DATE: 2026-01-06                                     ║\n" ++
  "║ TOTAL PREDICTIONS: 9                                        ║\n" ++
  "║ MIN PASSING: 6/9 (67%)                                      ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║ STRUCTURAL (4):                                             ║\n" ++
  "║   S1. Mode families → EEG frequency bands                   ║\n" ++
  "║   S2. φ-levels → amplitude quantization                     ║\n" ++
  "║   S3. Conjugate pairs → cross-frequency coupling            ║\n" ++
  "║   S4. Graph distance → priming effects                      ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║ COMPOSITIONAL (2):                                          ║\n" ++
  "║   C1. Synonym sentences → same LNAL motif                   ║\n" ++
  "║   C2. Compatible tokens → co-activation                     ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║ ALIGNMENT (3):                                              ║\n" ++
  "║   A1. Similar words → nearby tokens                         ║\n" ++
  "║   A2. Translation pairs → same tokens                       ║\n" ++
  "║   A3. Antonyms → distant tokens                             ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#eval frozenPredictionsSummary

end IndisputableMonolith.Verification.Preregistered.MeaningLandscape
