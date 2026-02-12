/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.PhenomenalTime

/-!
# ULQ Qualia and Memory

This module formalizes the relationship between qualia and memory:
how past experiences affect present qualia, and how qualia are encoded,
stored, and recalled.

## Key Insight

Memory is not storage of qualia but **reconstruction**. When we "remember,"
we don't retrieve stored qualia but re-derive them from encoded patterns.
The re-derived qualia may differ from the original (memory distortion).

## Physical Basis

| Physical Structure | Memory Aspect |
|-------------------|---------------|
| WToken encoding | Memory trace |
| Re-derivation | Recall |
| Pattern degradation | Forgetting |
| Mode preservation | Memory type |

## Types of Memory

1. **Episodic**: Complete experiential moments (mode + intensity + valence + temporal)
2. **Semantic**: Mode-only (factual knowledge without experiential quality)
3. **Procedural**: Intensity patterns (skills, habits)
4. **Emotional**: Valence traces (feelings without content)
-/

namespace IndisputableMonolith.ULQ.Memory

open IndisputableMonolith
open ULQ
open PhenomenalTime

/-! ## Memory Traces -/

/-- A memory trace encodes a past qualia -/
structure MemoryTrace where
  /-- Original qualia mode -/
  mode : QualiaMode
  /-- Intensity at encoding -/
  intensity : IntensityLevel
  /-- Valence at encoding -/
  valence_sign : Int  -- -1, 0, or 1 (simplified)
  /-- Valence sign is bounded to {-1, 0, 1} -/
  valence_sign_bounded : valence_sign = -1 ∨ valence_sign = 0 ∨ valence_sign = 1
  /-- Temporal marker (when encoded) -/
  encoding_time : ℕ
  /-- Trace strength (degrades over time) -/
  strength : ℕ  -- 0-100
  /-- Strength bounded -/
  strength_bounded : strength ≤ 100
  deriving Repr

/-- Create a memory trace from qualia -/
noncomputable def encodeQualia (q : QualiaSpace) (time : ℕ) : MemoryTrace where
  mode := q.mode
  intensity := q.intensity
  valence_sign := if q.valence.value > 0 then 1 else if q.valence.value < 0 then -1 else 0
  valence_sign_bounded := by
    simp only [ite_eq_left_iff, ite_eq_right_iff]
    by_cases h1 : q.valence.value > 0 <;> by_cases h2 : q.valence.value < 0 <;> simp [h1, h2]
  encoding_time := time
  strength := 100
  strength_bounded := by norm_num

/-! ## Memory Types -/

/-- Types of memory based on what is preserved -/
inductive MemoryType
  | Episodic      -- Full experiential memory
  | Semantic      -- Factual (mode only)
  | Procedural    -- Skill-based (intensity patterns)
  | Emotional     -- Valence only
  deriving DecidableEq, Repr

/-- Determine memory type from trace completeness -/
def classifyMemory (trace : MemoryTrace) : MemoryType :=
  if trace.strength > 75 then .Episodic
  else if trace.mode.k.val ≠ 0 ∧ trace.strength > 50 then .Semantic
  else if trace.intensity.level.val > 0 ∧ trace.strength > 25 then .Procedural
  else .Emotional

/-! ## Forgetting -/

/-- Memory decay rate (strength lost per τ₀ cycle) -/
def decayRate : ℕ := 5

/-- Apply forgetting to a memory trace -/
def applyForgetting (trace : MemoryTrace) (elapsed_cycles : ℕ) : MemoryTrace where
  mode := trace.mode
  intensity := trace.intensity
  valence_sign := trace.valence_sign
  valence_sign_bounded := trace.valence_sign_bounded
  encoding_time := trace.encoding_time
  strength := trace.strength - min trace.strength (elapsed_cycles * decayRate)
  strength_bounded := by
    have h := trace.strength_bounded
    omega

/-- Forgetting reduces strength -/
theorem forgetting_reduces_strength (trace : MemoryTrace) (cycles : ℕ) (h : cycles > 0) :
    (applyForgetting trace cycles).strength ≤ trace.strength := by
  simp only [applyForgetting]
  omega

/-- Complete forgetting after enough time -/
theorem complete_forgetting (trace : MemoryTrace) :
    (applyForgetting trace 20).strength = 0 ∨
    (applyForgetting trace 20).strength = trace.strength - 100 := by
  simp only [applyForgetting, decayRate]
  omega

/-! ## Recall -/

/-- Recalled qualia may differ from original -/
structure RecalledQualia where
  /-- The reconstructed qualia -/
  qualia : QualiaSpace
  /-- Confidence in recall (from trace strength) -/
  confidence : ℕ
  /-- Confidence bounded -/
  confidence_bounded : confidence ≤ 100
  /-- Memory type -/
  memory_type : MemoryType

/-- PROVEN: Valence sign from a memory trace is bounded to [-1, 1] -/
lemma valence_sign_real_bounded (trace : MemoryTrace) :
    -1 ≤ (trace.valence_sign : ℝ) ∧ (trace.valence_sign : ℝ) ≤ 1 := by
  rcases trace.valence_sign_bounded with h | h | h <;> simp [h]

/-- Recall qualia from memory trace -/
noncomputable def recallFromTrace (trace : MemoryTrace) : RecalledQualia where
  qualia := {
    mode := trace.mode
    intensity := trace.intensity
    valence := {
      value := (trace.valence_sign : ℝ)
      bounded := valence_sign_real_bounded trace
    }
    temporal := {
      tau := ⟨3, by norm_num⟩  -- Recalled as "past"
    }
  }
  confidence := trace.strength
  confidence_bounded := trace.strength_bounded
  memory_type := classifyMemory trace

/-- Recall confidence matches trace strength -/
theorem recall_confidence_eq_strength (trace : MemoryTrace) :
    (recallFromTrace trace).confidence = trace.strength := rfl

/-! ## Memory Distortion -/

/-- Ways memory can be distorted -/
inductive MemoryDistortion
  | Fading         -- Loss of detail
  | Intensification -- Emotion amplified
  | Reconstruction -- Details changed
  | Confabulation  -- False additions
  deriving DecidableEq, Repr

/-- Detect memory distortion by comparing trace to recalled -/
def detectDistortion (trace : MemoryTrace) (recalled : RecalledQualia) : Option MemoryDistortion :=
  if recalled.confidence < 25 then some .Fading
  else if recalled.qualia.intensity.level > trace.intensity.level then some .Intensification
  else if recalled.qualia.mode.k ≠ trace.mode.k then some .Reconstruction
  else none

/-! ## Memory Consolidation -/

/-- Memory consolidation strengthens traces -/
def consolidate (trace : MemoryTrace) (rehearsals : ℕ) : MemoryTrace where
  mode := trace.mode
  intensity := trace.intensity
  valence_sign := trace.valence_sign
  valence_sign_bounded := trace.valence_sign_bounded
  encoding_time := trace.encoding_time
  strength := min 100 (trace.strength + rehearsals * 10)
  strength_bounded := by omega

/-- Consolidation increases or maintains strength -/
theorem consolidation_strengthens (trace : MemoryTrace) (rehearsals : ℕ) :
    (consolidate trace rehearsals).strength ≥ trace.strength := by
  simp only [consolidate]
  exact le_min (trace.strength_bounded) (Nat.le_add_right _ _)

/-! ## Emotional Memory Enhancement -/

/-- Emotional memories are stronger -/
def emotionalEnhancement (trace : MemoryTrace) : MemoryTrace :=
  if h : trace.valence_sign ≠ 0 then
    { trace with
      strength := min 100 (trace.strength + 20)
      strength_bounded := by simp [min_le_left] }
  else trace

/-- Emotional memories decay slower -/
def emotionalDecay (trace : MemoryTrace) (cycles : ℕ) : MemoryTrace :=
  if trace.valence_sign ≠ 0 then
    applyForgetting trace (cycles / 2)  -- Half decay rate
  else
    applyForgetting trace cycles

/-! ## Memory Integration -/

/-- Multiple traces can be integrated into unified memory -/
structure IntegratedMemory where
  /-- Component traces -/
  traces : List MemoryTrace
  /-- Non-empty -/
  nonempty : traces ≠ []
  /-- All from same event (similar encoding time) -/
  coherent : ∀ t1 t2, t1 ∈ traces → t2 ∈ traces →
    (t1.encoding_time : Int) - t2.encoding_time < 10

/-- Average strength of integrated memory -/
def integratedStrength (im : IntegratedMemory) : ℕ :=
  (im.traces.map MemoryTrace.strength).sum / im.traces.length

/-! ## Priming Effects -/

/-- Priming: recent qualia affect memory recall -/
structure PrimingEffect where
  /-- The priming qualia -/
  prime : QualiaSpace
  /-- Affected memory traces -/
  affected_traces : List MemoryTrace
  /-- Priming strength (0-100) -/
  strength : ℕ

/-- Mode-congruent priming (same mode = stronger recall) -/
def modeCongruentPriming (prime : QualiaSpace) (trace : MemoryTrace) : Bool :=
  prime.mode.k = trace.mode.k

/-- Valence-congruent priming (same valence sign = stronger recall) -/
noncomputable def valenceCongruentPriming (prime : QualiaSpace) (trace : MemoryTrace) : Bool :=
  let prime_sign : Int := if prime.valence.value > 0 then 1 else if prime.valence.value < 0 then -1 else 0
  prime_sign = trace.valence_sign

/-! ## Status Report -/

def memory_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ULQ QUALIA AND MEMORY                              ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  MEMORY TRACES: Encoded qualia patterns                      ║\n" ++
  "║  MEMORY TYPES:                                               ║\n" ++
  "║  • Episodic: Full experiential memory                        ║\n" ++
  "║  • Semantic: Factual (mode only)                             ║\n" ++
  "║  • Procedural: Skills (intensity patterns)                   ║\n" ++
  "║  • Emotional: Valence traces                                 ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  FORGETTING: Strength decay over τ₀ cycles                   ║\n" ++
  "║  CONSOLIDATION: Rehearsal strengthens traces                 ║\n" ++
  "║  DISTORTION: Fading, intensification, reconstruction         ║\n" ++
  "║  EMOTIONAL ENHANCEMENT: Valenced memories stronger           ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  KEY INSIGHT:                                                ║\n" ++
  "║  Memory = RECONSTRUCTION, not storage.                       ║\n" ++
  "║  Recalled qualia are re-derived, not retrieved.              ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check memory_status

end IndisputableMonolith.ULQ.Memory
