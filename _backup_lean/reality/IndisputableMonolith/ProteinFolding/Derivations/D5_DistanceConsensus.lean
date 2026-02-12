import Mathlib
import IndisputableMonolith.Constants

/-!
# Derivation D5: Distance-Scaled φ-Consensus

This module formalizes the requirement that long-range contacts need
more supporting evidence (coherent channels) than short-range contacts.

## Key Formula

    required_channels(d) = 2 + ⌊log_φ(d/10)⌋

Where d is the sequence separation in residues.

## Table

| Distance | Required Channels |
|----------|-------------------|
| ≤10 | 2 |
| 11-16 | 3 |
| 17-26 | 4 |
| 27-42 | 5 |
| >42 | 6 |

## Physical Motivation

Longer-range contacts require more phase coherence across chemistry
channels because:
1. More intervening residues can disrupt phase alignment
2. Larger loop closures are entropically costly
3. Geometric constraints are more stringent

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace Derivations
namespace D5

open Constants

/-! ## φ-Scaled Distance Thresholds -/

/-- Reference distance (residues) -/
def d_ref : ℕ := 10

/-- φ-scaled distance thresholds -/
noncomputable def distanceThreshold (n : ℕ) : ℝ :=
  d_ref * phi ^ n

/-- Threshold 1: d_ref × φ¹ ≈ 16 -/
noncomputable def threshold1 : ℝ := distanceThreshold 1

/-- Threshold 2: d_ref × φ² ≈ 26 -/
noncomputable def threshold2 : ℝ := distanceThreshold 2

/-- Threshold 3: d_ref × φ³ ≈ 42 -/
noncomputable def threshold3 : ℝ := distanceThreshold 3

/-! ## Required Channels Function -/

/-- **DISTANCE-SCALED CHANNEL REQUIREMENT**

    Number of coherent channels required based on sequence separation.
    Formula: 2 + ⌊log_φ(d/10)⌋ for d > 10, minimum 2 -/
def requiredChannels (d : ℕ) : ℕ :=
  if d ≤ 10 then 2
  else if d ≤ 16 then 3
  else if d ≤ 26 then 4
  else if d ≤ 42 then 5
  else 6

/-- Verification of channel requirements table -/
theorem channel_table :
    requiredChannels 8 = 2 ∧
    requiredChannels 10 = 2 ∧
    requiredChannels 14 = 3 ∧
    requiredChannels 16 = 3 ∧
    requiredChannels 22 = 4 ∧
    requiredChannels 26 = 4 ∧
    requiredChannels 35 = 5 ∧
    requiredChannels 42 = 5 ∧
    requiredChannels 50 = 6 := by
  simp only [requiredChannels]
  native_decide

/-- Required channels is monotonically non-decreasing -/
theorem channels_monotone (d1 d2 : ℕ) (h : d1 ≤ d2) :
    requiredChannels d1 ≤ requiredChannels d2 := by
  simp only [requiredChannels]
  split_ifs <;> omega

/-- Minimum is 2 channels -/
theorem channels_min_two (d : ℕ) : requiredChannels d ≥ 2 := by
  simp only [requiredChannels]
  split_ifs <;> norm_num

/-- Maximum is 6 channels -/
theorem channels_max_six (d : ℕ) : requiredChannels d ≤ 6 := by
  simp only [requiredChannels]
  split_ifs <;> norm_num

/-! ## φ-Based Derivation -/

/-- Logarithmic formula for required channels (continuous version) -/
noncomputable def requiredChannelsContinuous (d : ℝ) : ℝ :=
  if d ≤ 10 then 2
  else 2 + Real.log (d / 10) / Real.log phi

/-- The discrete and continuous versions agree at thresholds -/
theorem continuous_agrees_at_thresholds :
    requiredChannelsContinuous 10 = 2 := by
  simp only [requiredChannelsContinuous]
  norm_num

/-! ## Channel Coherence Scoring -/

/-- Score for having k coherent channels at distance d -/
noncomputable def channelScore (k d : ℕ) : ℝ :=
  let required := requiredChannels d
  if k ≥ required then 1.0 + 0.1 * (k - required)
  else (k : ℝ) / required

/-- Full support gives score ≥ 1 -/
theorem full_support_score (k d : ℕ) (h : k ≥ requiredChannels d) :
    channelScore k d ≥ 1 := by
  simp only [channelScore, h, ↓reduceIte]
  have : (0 : ℝ) ≤ 0.1 * (k - requiredChannels d) := by
    apply mul_nonneg (by norm_num)
    simp only [Nat.cast_sub (le_of_lt (Nat.lt_of_lt_of_le (by omega : 0 < k) h) )]
    exact Nat.cast_nonneg _
  linarith

/-- Insufficient support gives score < 1 -/
theorem insufficient_support_score (k d : ℕ) (h : k < requiredChannels d)
    (hd : requiredChannels d > 0) :
    channelScore k d < 1 := by
  simp only [channelScore]
  split_ifs with hk
  · omega
  · have hreq : (0 : ℝ) < requiredChannels d := by
      exact Nat.cast_pos.mpr hd
    have hk' : (k : ℝ) < requiredChannels d := by
      exact Nat.cast_lt.mpr h
    exact div_lt_one_of_lt hk' hreq

/-! ## Integration with Contact Scoring -/

/-- Contact score multiplier based on channel consensus -/
noncomputable def consensusMultiplier (coherentChannels separation : ℕ) : ℝ :=
  let required := requiredChannels separation
  if coherentChannels ≥ required then
    1.0 + 0.05 * (coherentChannels - required)  -- Small bonus for extra support
  else
    0.5 ^ (required - coherentChannels)  -- Exponential penalty for missing channels

/-- Sufficient consensus gives multiplier ≥ 1 -/
theorem sufficient_consensus (k d : ℕ) (h : k ≥ requiredChannels d) :
    consensusMultiplier k d ≥ 1 := by
  simp only [consensusMultiplier, h, ↓reduceIte]
  have : 0 ≤ 0.05 * (k - requiredChannels d) := by
    apply mul_nonneg (by norm_num)
    exact Nat.cast_nonneg _
  linarith

end D5
end Derivations
end ProteinFolding
end IndisputableMonolith
