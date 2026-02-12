import Mathlib
import IndisputableMonolith.MusicTheory.HarmonicModes
import IndisputableMonolith.Foundation.PhiForcing
import IndisputableMonolith.Patterns

/-!
# Rhythm: 8-Tick Structure in the Time Domain

This module derives **musical rhythm from the RS 8-tick structure**.

## Core Insight

The 8-tick periodicity (T7: 2^D for D=3) is the foundation of:

1. **Beat subdivision**: Common time (4/4) = 8 eighth notes
2. **Metric hierarchy**: 8 = 2³ gives 3 levels of subdivision
3. **Swing feel**: Asymmetric 8-tick divisions (5+3, 3+5)

## The 8-Beat Framework

Musical meter emerges from the same structure as physical recognition:

| Level | Subdivision | Musical Term |
|-------|-------------|--------------|
| 1 | 8 ticks | Eighth notes |
| 2 | 4 pairs | Quarter notes |
| 3 | 2 halves | Half notes |
| 4 | 1 whole | Whole measure |

This is exactly the binary tree structure of the 3-cube (Q₃).

## Connection to Time Signatures

Common time signatures and their 8-tick interpretations:
- 4/4 (common time): 8 eighth notes = 8 ticks
- 3/4 (waltz): 6 eighth notes ≈ 8 ticks with 2 silent
- 6/8 (compound duple): 6 + 2 = 8, grouped as 3+3+2
- 5/4 (asymmetric): 5 = Fibonacci, relates to φ

-/

namespace IndisputableMonolith
namespace MusicTheory
namespace Rhythm

open HarmonicModes

/-! ## The 8-Tick Beat -/

/-- A rhythmic tick within the 8-beat cycle. -/
abbrev Tick := Fin 8

/-- A beat pattern: which ticks are "on" (accented/sounded). -/
abbrev BeatPattern := Fin 8 → Bool

/-- The number of ticks in a complete cycle. -/
def ticksPerCycle : ℕ := 8

/-- The 8-tick cycle equals 2³ (from D=3). -/
theorem eight_ticks_from_dimension : ticksPerCycle = 2^3 := rfl

/-! ## Basic Beat Patterns -/

/-- All ticks on (continuous sound). -/
def allOnPattern : BeatPattern := fun _ => true

/-- Alternating ticks (2-feel). -/
def alternatingPattern : BeatPattern := fun t => t.val % 2 = 0

/-- Every 4th tick (quarter note feel). -/
def quarterNotePattern : BeatPattern := fun t => t.val % 4 = 0

/-- Downbeat only (whole note feel). -/
def downbeatPattern : BeatPattern := fun t => t.val = 0

/-- The number of active ticks in a pattern. -/
def patternDensity (p : BeatPattern) : ℕ :=
  (Finset.univ.filter fun t => p t).card

theorem all_on_density : patternDensity allOnPattern = 8 := by
  simp [patternDensity, allOnPattern]

theorem alternating_density : patternDensity alternatingPattern = 4 := by
  simp only [patternDensity, alternatingPattern]
  native_decide

theorem quarter_note_density : patternDensity quarterNotePattern = 2 := by
  simp only [patternDensity, quarterNotePattern]
  native_decide

theorem downbeat_density : patternDensity downbeatPattern = 1 := by
  simp only [patternDensity, downbeatPattern]
  native_decide

/-! ## Metric Hierarchy -/

/-- The metric weight of a tick: how "strong" it is in the hierarchy.
    Tick 0 is strongest (downbeat), then 4, then 2,6, then odd ticks. -/
def metricWeight (t : Tick) : ℕ :=
  if t.val = 0 then 4
  else if t.val = 4 then 3
  else if t.val % 2 = 0 then 2
  else 1

/-- The downbeat has maximum weight. -/
theorem downbeat_max_weight : metricWeight 0 = 4 := by simp [metricWeight]

/-- Tick 4 has second-highest weight (back-beat). -/
theorem backbeat_weight : metricWeight 4 = 3 := by
  simp only [metricWeight]
  rfl

/-- Odd ticks have minimum weight (off-beats). -/
theorem offbeat_weight (t : Tick) (ht : t.val % 2 = 1) : metricWeight t = 1 := by
  simp only [metricWeight]
  have h0 : t.val ≠ 0 := by omega
  have h4 : t.val ≠ 4 := by omega
  have h2 : t.val % 2 ≠ 0 := by omega
  simp only [h0, ↓reduceIte, h4, h2]

/-! ## Swing and Groove -/

/-- A swing ratio: how unequal the subdivision is.
    Ratio 1 = straight, ratio > 1 = swing (first tick longer).
    Common values: 3/2 (triplet swing), 5/3 (light swing), 7/5 (heavy swing) -/
structure SwingRatio where
  first : ℕ  -- Duration of first tick
  second : ℕ -- Duration of second tick
  first_pos : 0 < first
  second_pos : 0 < second

/-- Straight eighths: equal subdivision. -/
def straightSwing : SwingRatio := ⟨1, 1, by norm_num, by norm_num⟩

/-- Triplet swing: 2:1 ratio (like triplet feel). -/
def tripletSwing : SwingRatio := ⟨2, 1, by norm_num, by norm_num⟩

/-- Light swing: 3:2 ratio (the perfect fifth!). -/
def lightSwing : SwingRatio := ⟨3, 2, by norm_num, by norm_num⟩

/-- The swing ratio as a real number. -/
noncomputable def SwingRatio.toReal (s : SwingRatio) : ℝ := s.first / s.second

/-- Light swing has ratio 3/2 = the perfect fifth. -/
theorem light_swing_is_fifth : lightSwing.toReal = 3/2 := by
  simp [SwingRatio.toReal, lightSwing]

/-- A φ-based swing ratio. φ ≈ 1.618, so we approximate as 8:5 ≈ 1.6 -/
def goldenSwing : SwingRatio := ⟨8, 5, by norm_num, by norm_num⟩

/-- The golden swing ratio approximates φ.
    8/5 = 1.6, φ ≈ 1.618, so |8/5 - φ| ≈ 0.018 < 0.02 -/
theorem golden_swing_approx_phi :
    |goldenSwing.toReal - Foundation.PhiForcing.φ| < 0.02 := by
  simp [SwingRatio.toReal, goldenSwing, Foundation.PhiForcing.φ]
  -- 8/5 = 1.6, φ = (1 + √5)/2 ≈ 1.6180339...
  -- |1.6 - 1.618...| ≈ 0.018 < 0.02
  -- Numerical verification: √5 ∈ (2.23, 2.24), so φ ∈ (1.615, 1.62)
  -- |1.6 - 1.615| = 0.015 < 0.02 ✓
  have h_sqrt5_lower : (2.23 : ℝ) < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2.23) (by norm_num : (0 : ℝ) ≤ 5)]
    norm_num
  have h_sqrt5_upper : Real.sqrt 5 < 2.24 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) ≤ 5)]
    constructor
    · norm_num
    · norm_num
  -- φ = (1 + √5)/2 is between (1 + 2.23)/2 = 1.615 and (1 + 2.24)/2 = 1.62
  have h_phi_bounds : 1.615 < Foundation.PhiForcing.φ ∧ Foundation.PhiForcing.φ < 1.62 := by
    constructor <;> { unfold Foundation.PhiForcing.φ; linarith }
  -- |1.6 - φ| < max(|1.6 - 1.615|, |1.6 - 1.62|) = 0.02
  rw [abs_sub_lt_iff]
  constructor <;> linarith [h_phi_bounds.1, h_phi_bounds.2]

/-! ## Time Signatures and 8-Tick Mapping -/

/-- A time signature. -/
structure TimeSignature where
  beats : ℕ      -- Beats per measure
  noteValue : ℕ  -- Note value getting one beat (4 = quarter, 8 = eighth)
  beats_pos : 0 < beats
  noteValue_pos : 0 < noteValue

/-- Common time (4/4). -/
def commonTime : TimeSignature := ⟨4, 4, by norm_num, by norm_num⟩

/-- Waltz time (3/4). -/
def waltzTime : TimeSignature := ⟨3, 4, by norm_num, by norm_num⟩

/-- Compound duple (6/8). -/
def compoundDuple : TimeSignature := ⟨6, 8, by norm_num, by norm_num⟩

/-- The number of eighth notes in a measure. -/
def eighthsPerMeasure (ts : TimeSignature) : ℕ :=
  ts.beats * (8 / ts.noteValue)

/-- Common time has 8 eighth notes per measure = 8 ticks. -/
theorem common_time_eight_ticks : eighthsPerMeasure commonTime = 8 := by
  simp [eighthsPerMeasure, commonTime]

/-- 6/8 has 6 eighth notes per measure. -/
theorem compound_duple_six_eighths : eighthsPerMeasure compoundDuple = 6 := by
  simp [eighthsPerMeasure, compoundDuple]

/-! ## Polyrhythm and the 8-Tick Structure -/

/-- A polyrhythm: two simultaneous patterns with different densities. -/
structure Polyrhythm where
  pattern1 : BeatPattern
  pattern2 : BeatPattern

/-- The classic 3-against-4 polyrhythm.
    Pattern 1: ticks 0, 2, 5 (approximately dividing 8 into 3)
    Pattern 2: ticks 0, 2, 4, 6 (dividing 8 into 4) -/
def threeAgainstFour : Polyrhythm := {
  pattern1 := fun t => t.val = 0 ∨ t.val = 3 ∨ t.val = 5
  pattern2 := alternatingPattern
}

/-- Ticks where both patterns coincide. -/
def Polyrhythm.coincidence (p : Polyrhythm) : BeatPattern :=
  fun t => p.pattern1 t ∧ p.pattern2 t

/-! ## The Breath Cycle: 1024 Ticks -/

/-- The full breath cycle: 1024 = 2^10 = 128 × 8 ticks. -/
def breathCycleTicks : ℕ := 1024

/-- The breath cycle is 128 eight-tick cycles. -/
theorem breath_is_128_eights : breathCycleTicks = 128 * ticksPerCycle := by
  simp [breathCycleTicks, ticksPerCycle]

/-- The breath cycle has a flip at the midpoint (512). -/
def breathFlipPoint : ℕ := 512

theorem breath_flip_is_midpoint : breathFlipPoint = breathCycleTicks / 2 := by
  simp [breathFlipPoint, breathCycleTicks]

/-! ## Musical Tempo and τ₀ -/

/-- Typical musical tempos in BPM (beats per minute).
    Mapped to τ₀ multiples in the Recognition framework. -/
def typicalTempos : List ℕ := [60, 72, 80, 90, 100, 108, 120, 132, 144]

/-- The tempo 60 BPM means 1 beat per second.
    If one beat = 8 ticks, then at 60 BPM we have 8 ticks/second.
    This gives a tick duration of 125 ms. -/
noncomputable def tickDurationAt60BPM : ℝ := 1 / 8  -- seconds

/-- Common tempos often relate to φ:
    - 72 BPM ≈ 60 × 1.2 ≈ 60 / (1/φ + 0.2)
    - 120 BPM = 60 × 2 (octave)
    - 90 BPM ≈ 60 × φ^0.5 ≈ 60 × 1.272 ≈ 76.3
    The relationship is approximate but suggestive. -/
theorem tempo_120_is_octave_of_60 : 120 = 60 * 2 := by norm_num

end Rhythm
end MusicTheory
end IndisputableMonolith
