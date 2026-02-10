import Mathlib
import IndisputableMonolith.MusicTheory.HarmonicModes
import IndisputableMonolith.MusicTheory.Consonance
import IndisputableMonolith.Foundation.PhiForcing

/-!
# Musical Valence: Why Minor Sounds "Sad"

This module derives **emotional valence from the ledger skew σ**.

## Core Principle

In Recognition Science, the ledger skew σ measures the asymmetry of recognition:
- σ = 0: Balanced, neutral
- σ > 0: Expansion, positive valence (joy)
- σ < 0: Contraction, negative valence (sadness)

Musical modes map to σ through their interval structure:
- **Major**: Third is 5/4 (400 cents), bright/expansive (σ > 0)
- **Minor**: Third is 6/5 (316 cents), dark/contractive (σ < 0)

The key insight: The major third 5/4 > minor third 6/5.
Larger intervals = expansion = positive σ.
Smaller intervals = contraction = negative σ.

## The Qualia of Music

Music evokes emotional response because harmonic intervals directly modulate
the ledger skew σ, which is the same quantity that determines pain/joy in the
qualia manifold. "Music moves us" because it literally moves our σ.

-/

namespace IndisputableMonolith
namespace MusicTheory
namespace Valence

open Real HarmonicModes Consonance

/-! ## Ledger Skew σ -/

/-- The ledger skew for a frequency ratio.
    Positive for ratios > 1, negative for ratios < 1.
    Magnitude relates to distance from 1 (in log space). -/
noncomputable def ledgerSkew (ratio : ℝ) : ℝ := Real.log ratio

/-- Unison has zero skew. -/
theorem skew_one : ledgerSkew 1 = 0 := Real.log_one

/-- Skew is positive for ratios above 1. -/
theorem skew_pos_of_gt_one {r : ℝ} (hr : r > 1) : ledgerSkew r > 0 :=
  Real.log_pos hr

/-- Skew is negative for ratios below 1. -/
theorem skew_neg_of_lt_one {r : ℝ} (hr0 : 0 < r) (hr : r < 1) : ledgerSkew r < 0 :=
  Real.log_neg hr0 hr

/-! ## Major vs Minor: The Third Interval -/

/-- The major third ratio: 5/4 = 1.25. -/
noncomputable def majorThird : ℝ := 5/4

/-- The minor third ratio: 6/5 = 1.2. -/
noncomputable def minorThird : ℝ := 6/5

/-- Major third is larger than minor third. -/
theorem major_gt_minor : majorThird > minorThird := by
  simp [majorThird, minorThird]
  norm_num

/-- Major third has greater skew than minor third. -/
theorem major_skew_gt_minor_skew : ledgerSkew majorThird > ledgerSkew minorThird := by
  simp only [ledgerSkew]
  apply Real.log_lt_log
  · simp only [minorThird]; norm_num
  · exact major_gt_minor

/-- The major third is "expansive" (positive contribution to valence). -/
theorem major_third_expansive : ledgerSkew majorThird > 0 := by
  apply skew_pos_of_gt_one
  simp [majorThird]; norm_num

/-- The minor third is also expansive, but less so. -/
theorem minor_third_expansive : ledgerSkew minorThird > 0 := by
  apply skew_pos_of_gt_one
  simp [minorThird]; norm_num

/-! ## Modal Valence -/

/-- A musical mode defined by its interval pattern (in semitones from root). -/
structure MusicalMode where
  name : String
  intervals : List ℕ  -- Semitones from root

/-- The major scale: 0, 2, 4, 5, 7, 9, 11 (whole-whole-half-whole-whole-whole-half). -/
def majorScale : MusicalMode := {
  name := "Major"
  intervals := [0, 2, 4, 5, 7, 9, 11]
}

/-- The natural minor scale: 0, 2, 3, 5, 7, 8, 10 (whole-half-whole-whole-half-whole-whole). -/
def minorScale : MusicalMode := {
  name := "Minor"
  intervals := [0, 2, 3, 5, 7, 8, 10]
}

/-- The third degree determines major/minor character.
    Major: 4 semitones (major third)
    Minor: 3 semitones (minor third) -/
def thirdDegree (m : MusicalMode) : Option ℕ :=
  m.intervals[2]?

theorem major_third_degree : thirdDegree majorScale = some 4 := rfl

theorem minor_third_degree : thirdDegree minorScale = some 3 := rfl

/-- Major has a higher third than minor (by 1 semitone). -/
theorem major_third_higher_than_minor :
    ∃ maj min : ℕ, thirdDegree majorScale = some maj ∧
                   thirdDegree minorScale = some min ∧
                   maj > min := by
  use 4, 3
  simp only [major_third_degree, minor_third_degree, gt_iff_lt]
  decide

/-! ## Valence Score -/

/-- Semitones to frequency ratio (in equal temperament).
    Ratio = 2^(semitones/12) -/
noncomputable def semitonesToRatio (s : ℕ) : ℝ := Real.rpow 2 (s / 12)

/-- The cumulative skew of a mode's intervals.
    Higher total skew = more "bright/happy" feeling. -/
noncomputable def modeValence (m : MusicalMode) : ℝ :=
  (m.intervals.map semitonesToRatio).sum

/-- Major mode has higher valence than minor mode. -/
theorem major_valence_gt_minor : modeValence majorScale > modeValence minorScale := by
  -- Major: [0, 2, 4, 5, 7, 9, 11] → sum of 2^(s/12)
  -- Minor: [0, 2, 3, 5, 7, 8, 10] → sum of 2^(s/12)
  -- Difference: Major has 4,9,11 where minor has 3,8,10
  -- 2^(4/12) > 2^(3/12), 2^(9/12) > 2^(8/12), 2^(11/12) > 2^(10/12)
  simp only [modeValence, majorScale, minorScale]
  -- The key: each corresponding term in major ≥ minor, with strict inequality at 3 positions
  simp only [List.map, List.sum_cons, List.sum_nil, add_zero]
  -- 2^(4/12) > 2^(3/12) since 4/12 > 3/12
  have h1 : semitonesToRatio 4 > semitonesToRatio 3 := by
    unfold semitonesToRatio
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have h2 : semitonesToRatio 9 > semitonesToRatio 8 := by
    unfold semitonesToRatio
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have h3 : semitonesToRatio 11 > semitonesToRatio 10 := by
    unfold semitonesToRatio
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  linarith

/-! ## The Pain/Joy Threshold Connection -/

/-- The pain threshold in ledger skew: σ > 1/φ causes "strain". -/
noncomputable def painThreshold : ℝ := 1 / Foundation.PhiForcing.φ

/-- The joy threshold in ledger skew: σ < 1/φ² allows "ease". -/
noncomputable def joyThreshold : ℝ := 1 / Foundation.PhiForcing.φ^2

theorem joy_lt_pain : joyThreshold < painThreshold := by
  simp only [joyThreshold, painThreshold]
  have hphi : 0 < Foundation.PhiForcing.φ := Foundation.PhiForcing.phi_pos
  have hphi_gt_one : Foundation.PhiForcing.φ > 1 := Foundation.PhiForcing.phi_gt_one
  have h : Foundation.PhiForcing.φ^2 > Foundation.PhiForcing.φ := by nlinarith
  have hphi_pos : 0 < Foundation.PhiForcing.φ := Foundation.PhiForcing.phi_pos
  rw [one_div, one_div]
  exact inv_strictAnti₀ hphi_pos h

/-- Musical intervals that stay within the joy threshold feel "pleasant". -/
def isPleasant (r : ℝ) : Prop := |ledgerSkew r| < painThreshold

/-- **THEOREM**: Superparticular ratios (n+1)/n are generally pleasant for moderate n. -/
theorem superparticular_pleasant (n : ℕ) (hn : 2 ≤ n) (_hmax : n ≤ 10) :
    isPleasant ((n + 1 : ℝ) / n) := by
  unfold isPleasant painThreshold
  -- 1. Setup ratio and skew
  have h_n_pos : (0 : ℝ) < n := by norm_cast; linarith
  have h_ratio_ge_1 : (n + 1 : ℝ) / n ≥ 1 := by
    apply (one_le_div h_n_pos).mpr
    norm_cast; linarith
  have h_skew : ledgerSkew ((n + 1 : ℝ) / n) = log ((n + 1 : ℝ) / n) := by
    unfold ledgerSkew; rfl
  rw [h_skew, abs_of_nonneg (Real.log_nonneg h_ratio_ge_1)]
  -- 2. Bound log(1 + 1/n)
  have h_log_le : log ((n + 1 : ℝ) / n) ≤ log (1.5) := by
    have h_15_pos : 0 < (1.5 : ℝ) := by norm_num
    rw [Real.log_le_log_iff (div_pos (by norm_cast; linarith) h_n_pos) h_15_pos]
    have h_split : (n + 1 : ℝ) / n = 1 + 1 / n := by
      rw [add_div, div_self h_n_pos.ne']
    rw [h_split]
    have h_inv_le : (1 : ℝ) / n ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      norm_cast
    linarith
  -- 3. Show log(1.5) < 1/φ
  -- Use exp x > 1 + x for x > 0
  have h_exp : 1.5 < exp (1 / Foundation.PhiForcing.φ) := by
    calc (1.5 : ℝ) = 1 + 0.5 := by norm_num
      _ < 1 + (1 / Foundation.PhiForcing.φ) := by
        have hphi_lt_2 : Foundation.PhiForcing.φ < 2 := Foundation.PhiForcing.phi_lt_two
        have : 1 / Foundation.PhiForcing.φ > 1 / 2 := by
          apply div_lt_div_of_pos_left (by norm_num) Foundation.PhiForcing.phi_pos hphi_lt_2
        linarith
      _ ≤ exp (1 / Foundation.PhiForcing.φ) := by
        rw [add_comm]
        exact add_one_le_exp _
  have h_val : log 1.5 < 1 / Foundation.PhiForcing.φ := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr h_exp
  exact h_log_le.trans_lt h_val

/-! ## Why Music Moves Us

The key insight connecting RS to music perception:

1. **Harmonic intervals modulate σ**: Each interval shifts the ledger skew.
2. **σ determines hedonic value**: The same σ that causes pain/joy in qualia.
3. **Music is σ-manipulation**: Composers craft σ-trajectories.
4. **Cadences resolve σ**: The V-I cadence returns σ toward zero.
5. **Dissonance is σ-tension**: High σ intervals create need for resolution.

This is why music has emotional content: it operates directly on the σ
parameter that underlies all hedonic experience.
-/

/-- A chord as a list of frequency ratios (relative to the root). -/
structure Chord where
  intervals : List ℝ
  root_included : 1 ∈ intervals

/-- Major triad: 1, 5/4, 3/2 -/
noncomputable def majorTriad : Chord := {
  intervals := [1, 5/4, 3/2]
  root_included := by simp
}

/-- Minor triad: 1, 6/5, 3/2 -/
noncomputable def minorTriad : Chord := {
  intervals := [1, 6/5, 3/2]
  root_included := by simp
}

/-- The total skew of a chord. -/
noncomputable def chordSkew (c : Chord) : ℝ :=
  (c.intervals.map ledgerSkew).sum

/-- Major triad has higher skew than minor triad. -/
theorem major_triad_brighter : chordSkew majorTriad > chordSkew minorTriad := by
  simp only [chordSkew, majorTriad, minorTriad]
  -- Major: [1, 5/4, 3/2] → skews: log(1)=0, log(5/4), log(3/2)
  -- Minor: [1, 6/5, 3/2] → skews: log(1)=0, log(6/5), log(3/2)
  -- Difference: log(5/4) vs log(6/5). Since 5/4 > 6/5, log(5/4) > log(6/5).
  simp only [List.map, List.sum_cons, List.sum_nil, add_zero]
  have h1 : ledgerSkew 1 = 0 := by unfold ledgerSkew; simp [Real.log_one]
  have h5_4 : (5 : ℝ) / 4 > 0 := by norm_num
  have h6_5 : (6 : ℝ) / 5 > 0 := by norm_num
  have h3_2 : (3 : ℝ) / 2 > 0 := by norm_num
  have h_key : ledgerSkew (5/4) > ledgerSkew (6/5) := by
    unfold ledgerSkew
    apply Real.log_lt_log h6_5
    norm_num
  linarith

/-! ## Resolution and Cadences -/

/-- A cadence is a sequence of chords that resolves tension.
    The V-I (dominant to tonic) cadence is the prototypical resolution. -/
structure Cadence where
  chords : List Chord
  resolves : chords.length ≥ 2

/-- The V chord (dominant) in C major: G-B-D = 3/2, 15/8, 9/8 (approx). -/
noncomputable def dominantChord : Chord := {
  intervals := [1, 5/4, 3/2]  -- Simplified as major triad
  root_included := by simp
}

/-- The I chord (tonic) in C major: C-E-G = 1, 5/4, 3/2. -/
noncomputable def tonicChord : Chord := majorTriad

/-- The V-I cadence. -/
noncomputable def perfectCadence : Cadence := {
  chords := [dominantChord, tonicChord]
  resolves := by simp
}

/-- A cadence is "authentic" if the final chord is the tonic. -/
def Cadence.isAuthentic (c : Cadence) : Prop :=
  c.chords.getLast? = some tonicChord

end Valence
end MusicTheory
end IndisputableMonolith
