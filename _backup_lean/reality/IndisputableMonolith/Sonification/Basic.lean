import Mathlib
import IndisputableMonolith.Water.WTokenIso

/-!
# Sonification (cross-octave observation layer)

Claim hygiene:
- **Definitions/Models** here define a *deterministic mapping* from existing
  formal objects (WTokens, strain scalars) into musical parameters.
- **Empirical correlations** (e.g. “consonance tracks RMSD”) must be stated as
  explicit hypotheses elsewhere (with falsifiers), not as theorems.

This file is intended to support the `Source-Super-rrf.txt` “WTOKEN TO MUSICAL NOTE”
and “STRAIN TO DETUNING” sections.
-/

namespace IndisputableMonolith.Sonification

open IndisputableMonolith

/-! ## Musical primitives -/

inductive ChordQuality : Type
  | major
  | minor
  | diminished
  | augmented
  | suspended
deriving DecidableEq, Repr

structure ChordSpec where
  root : Nat        -- MIDI note number (e.g. 60 = Middle C)
  quality : ChordQuality
deriving Repr

/-! ## WToken → chord mapping (model) -/

namespace WToken

open IndisputableMonolith.Water

def baseChordOfMode (mode : WTokenMode) (tau : TauOffset) : ChordSpec :=
  match mode with
  | .mode1_7 => ⟨60, .major⟩
  | .mode2_6 => ⟨64, .minor⟩
  | .mode3_5 => ⟨67, .diminished⟩
  | .mode4 =>
      match tau with
      | .tau0 => ⟨69, .augmented⟩
      | .tau2 => ⟨72, .suspended⟩

def phiLevelToOctaves : PhiLevel → Nat
  | .level0 => 0
  | .level1 => 1
  | .level2 => 2
  | .level3 => 3

def chordOf (w : WTokenSpec) : ChordSpec :=
  let base := baseChordOfMode w.mode w.tau_offset
  { base with root := base.root + 12 * phiLevelToOctaves w.phi_level }

lemma chordOf_root_ge_base (w : WTokenSpec) :
    (baseChordOfMode w.mode w.tau_offset).root ≤ (chordOf w).root := by
  dsimp [chordOf]
  simp

end WToken

/-! ## Strain → detuning (model) -/

noncomputable def detuneCents (strain : ℝ) : ℝ :=
  min (strain * 50) 100

lemma detuneCents_le_100 (strain : ℝ) : detuneCents strain ≤ 100 := by
  dsimp [detuneCents]
  exact min_le_right _ _

lemma detuneCents_nonneg_of_nonneg {strain : ℝ} (h : 0 ≤ strain) :
    0 ≤ detuneCents strain := by
  dsimp [detuneCents]
  have : 0 ≤ strain * 50 := mul_nonneg h (by norm_num)
  exact le_trans (le_min this (by norm_num)) (le_rfl)

/-! ## Audible resolution (perceptual constants) -/

/-- Just-Noticeable Difference in cents (pitch).
    Empirical literature: ~5-10 cents for trained listeners;
    we use 5 cents as a conservative threshold. -/
noncomputable def centsJND : ℝ := 5

/-- The detuning slope: strain is multiplied by this to get cents. -/
noncomputable def detuneSlope : ℝ := 50

/-- Saturation threshold: strains above this produce the same (max) detune. -/
noncomputable def saturationStrain : ℝ := 2  -- since 2 * 50 = 100 (max)

/-- Minimum strain difference needed for an audible pitch difference,
    assuming neither strain is in the saturated region. -/
noncomputable def minAudibleStrainDelta : ℝ := centsJND / detuneSlope

lemma minAudibleStrainDelta_value : minAudibleStrainDelta = 0.1 := by
  simp [minAudibleStrainDelta, centsJND, detuneSlope]
  norm_num

/-- In the linear (unsaturated) region, detuneCents is exactly `strain * 50`. -/
lemma detuneCents_linear {strain : ℝ} (h : strain * 50 ≤ 100) :
    detuneCents strain = strain * 50 := by
  simp [detuneCents, min_eq_left h]

/-- Two strains that are both unsaturated and differ by at least `minAudibleStrainDelta`
    produce detune values that differ by at least `centsJND` (audibly distinguishable). -/
theorem detune_distinguishable
    {s₁ s₂ : ℝ}
    (hUnsat₁ : s₁ * 50 ≤ 100)
    (hUnsat₂ : s₂ * 50 ≤ 100)
    (hDiff : minAudibleStrainDelta ≤ |s₁ - s₂|) :
    centsJND ≤ |detuneCents s₁ - detuneCents s₂| := by
  rw [detuneCents_linear hUnsat₁, detuneCents_linear hUnsat₂]
  -- |s₁ * 50 - s₂ * 50| = |s₁ - s₂| * 50
  have h : |s₁ * 50 - s₂ * 50| = |s₁ - s₂| * 50 := by
    have : s₁ * 50 - s₂ * 50 = (s₁ - s₂) * 50 := by ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (50 : ℝ) > 0)]
  rw [h]
  -- minAudibleStrainDelta * 50 = centsJND, so centsJND ≤ |s₁ - s₂| * 50
  have hSlope : centsJND = minAudibleStrainDelta * 50 := by
    simp only [minAudibleStrainDelta, centsJND, detuneSlope]
    ring
  rw [hSlope]
  exact mul_le_mul_of_nonneg_right hDiff (by norm_num : (0 : ℝ) ≤ 50)

/-- Corollary: if strains differ by ≥ 0.1 and both are ≤ 2, the sounds are distinguishable. -/
theorem audible_at_tenth_strain_unit
    {s₁ s₂ : ℝ}
    (h₁ : s₁ ≤ saturationStrain) (h₂ : s₂ ≤ saturationStrain)
    (hDiff : 0.1 ≤ |s₁ - s₂|) :
    centsJND ≤ |detuneCents s₁ - detuneCents s₂| := by
  have hUnsat₁ : s₁ * 50 ≤ 100 := by
    have hSat : saturationStrain * 50 = 100 := by simp [saturationStrain]; norm_num
    calc s₁ * 50 ≤ saturationStrain * 50 := by nlinarith
      _ = 100 := hSat
  have hUnsat₂ : s₂ * 50 ≤ 100 := by
    have hSat : saturationStrain * 50 = 100 := by simp [saturationStrain]; norm_num
    calc s₂ * 50 ≤ saturationStrain * 50 := by nlinarith
      _ = 100 := hSat
  have hMin : minAudibleStrainDelta ≤ |s₁ - s₂| := by
    rw [minAudibleStrainDelta_value]
    exact hDiff
  exact detune_distinguishable hUnsat₁ hUnsat₂ hMin

/-! ## Consonance metric (model) -/

noncomputable def consonance (rmsd defect stddev : ℝ) : ℝ :=
  1 / (1 + rmsd / 10 + defect / 10 + stddev / 5)

lemma consonance_pos_of_nonneg
    {rmsd defect stddev : ℝ}
    (hr : 0 ≤ rmsd) (hd : 0 ≤ defect) (hs : 0 ≤ stddev) :
    0 < consonance rmsd defect stddev := by
  have hden : 0 < (1 + rmsd / 10 + defect / 10 + stddev / 5) := by
    have : 0 ≤ rmsd / 10 + defect / 10 + stddev / 5 := by
      nlinarith [hr, hd, hs]
    linarith
  dsimp [consonance]
  exact one_div_pos.mpr hden

end IndisputableMonolith.Sonification
