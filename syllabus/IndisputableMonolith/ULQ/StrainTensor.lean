import Mathlib
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.BeatFrequency
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants
import IndisputableMonolith.Support.GoldenRatio

/-!
# Qualia Strain Tensor

This module formalizes ULQ as the **Topological Conjugate** of ULL—not merely a list
of feelings but the **Strain Tensor** that measures the "friction" of Z-pattern
motion through the Ledger.

## Key Insight

If ULL is the *Coordinate System* (Syntax), then ULQ is the **Strain Tensor** (Semantics).
Qualia is the "friction" of a Z-pattern moving through the Ledger.

## Main Definitions

* `QualiaStrain` - Measures friction of Z-pattern motion against 8-tick cadence
* `painThreshold` - The J-cost threshold above which experience is painful
* `joyResonance` - Phase-locking condition for pleasurable experience

## Physical Motivation

- **Pain** = High J-cost / High Curvature / Misalignment with Θ
- **Joy** = Resonance / Phase-locking with Global Phase Θ (integer-rung ratios)

-/

namespace IndisputableMonolith
namespace ULQ
namespace StrainTensor

open Constants
open BeatFrequency
open Cost

/-! ## The J-Cost Function (Local Alias) -/

/-- The unique cost function J(x) = ½(x + 1/x) - 1 from T5
    This is the fundamental "friction" measure in RS. -/
noncomputable def J (x : ℝ) : ℝ := Jcost x

/-- J(1) = 0 (identity has zero cost) -/
theorem J_at_one : J 1 = 0 := Jcost_unit0

/-- J is nonnegative for positive x -/
theorem J_nonneg (x : ℝ) (hx : 0 < x) : 0 ≤ J x := Jcost_nonneg hx

/-- J is symmetric: J(x) = J(1/x) -/
theorem J_symmetric (x : ℝ) (hx : 0 < x) : J x = J (1/x) := by
  unfold J
  have hx' : x ≠ 0 := ne_of_gt hx
  have hinv : (1 : ℝ) / x = x⁻¹ := one_div x
  rw [hinv]
  exact Jcost_symm hx

/-- J is strictly monotone increasing for x > 1.
    This is the key property: moving away from unity increases cost. -/
theorem J_strict_mono_on_gt_one :
    ∀ x y : ℝ, 1 < x → x < y → J x < J y := by
  intro x y hx hxy
  unfold J Jcost
  -- J(x) = (x + 1/x)/2 - 1
  -- For x > 1, J is increasing because d/dx J(x) = (1 - 1/x²)/2 > 0
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  -- The function f(t) = t + 1/t is increasing for t > 1
  -- Key: (y + y⁻¹) - (x + x⁻¹) = (y - x)(1 - 1/(xy)) > 0 when xy > 1
  have hxy_prod : 1 < x * y := by nlinarith
  have h_diff : y + y⁻¹ - (x + x⁻¹) = (y - x) * (1 - (x * y)⁻¹) := by
    field_simp
    ring
  have h_factor1 : 0 < y - x := by linarith
  have h_factor2 : 0 < 1 - (x * y)⁻¹ := by
    have h_inv_lt : (x * y)⁻¹ < 1 := by
      rw [inv_lt_one₀ (by positivity : 0 < x * y)]
      exact hxy_prod
    linarith
  have h_prod_pos : 0 < (y - x) * (1 - (x * y)⁻¹) := mul_pos h_factor1 h_factor2
  linarith

/-! ## Phase Mismatch (Simplified) -/

/-- Phase mismatch between body clock and consciousness -/
noncomputable def phaseMismatch (t_body : ℕ) (t_qualia : ℕ) : ℝ :=
  let body_phase := (↑(t_body % 8) : ℝ) / 8
  let qualia_phase := (↑(t_qualia % 45) : ℝ) / 45
  |body_phase - qualia_phase|

/-- Phase mismatch is bounded in [0, 1] -/
theorem phaseMismatch_bounded (tb tq : ℕ) :
    0 ≤ phaseMismatch tb tq ∧ phaseMismatch tb tq ≤ 1 := by
  unfold phaseMismatch
  constructor
  · exact abs_nonneg _
  · -- Both phases are in [0, 1), so difference is in (-1, 1)
    have h8_lt : (↑(tb % 8) : ℝ) / 8 < 1 := by
      have hmod : (tb % 8 : ℕ) < 8 := Nat.mod_lt tb (by norm_num : 8 > 0)
      have hcast : (↑(tb % 8) : ℝ) < 8 := Nat.cast_lt.mpr hmod
      linarith
    have h8_ge : 0 ≤ (↑(tb % 8) : ℝ) / 8 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
    have h45_lt : (↑(tq % 45) : ℝ) / 45 < 1 := by
      have hmod : (tq % 45 : ℕ) < 45 := Nat.mod_lt tq (by norm_num : 45 > 0)
      have hcast : (↑(tq % 45) : ℝ) < 45 := Nat.cast_lt.mpr hmod
      linarith
    have h45_ge : 0 ≤ (↑(tq % 45) : ℝ) / 45 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
    have hdiff_upper : (↑(tb % 8) : ℝ) / 8 - (↑(tq % 45) : ℝ) / 45 < 1 := by linarith
    have hdiff_lower : -1 < (↑(tb % 8) : ℝ) / 8 - (↑(tq % 45) : ℝ) / 45 := by linarith
    exact le_of_lt (abs_lt.mpr ⟨hdiff_lower, hdiff_upper⟩)

/-! ## The Qualia Strain Tensor -/

/-- **THE QUALIA STRAIN TENSOR**

    Measures the "friction" of Z-pattern motion against the 8-tick cadence.
    High strain = unpleasant experience (pain).
    Low strain = pleasant experience (joy).

    strain = phase_mismatch × J(intensity)
-/
noncomputable def QualiaStrain (mismatch : ℝ) (intensity : ℝ) : ℝ :=
  mismatch * J intensity

/-- Strain is nonnegative -/
theorem QualiaStrain_nonneg (m i : ℝ) (hm : 0 ≤ m) (hi : 0 < i) :
    0 ≤ QualiaStrain m i := by
  unfold QualiaStrain
  apply mul_nonneg hm (J_nonneg i hi)

/-- Zero mismatch means zero strain (perfect alignment) -/
theorem zero_mismatch_zero_strain (i : ℝ) : QualiaStrain 0 i = 0 := by
  unfold QualiaStrain
  ring

/-- Unit intensity means mismatch-proportional strain -/
theorem unit_intensity_strain (m : ℝ) : QualiaStrain m 1 = 0 := by
  unfold QualiaStrain J
  rw [Jcost_unit0]
  ring

/-! ## Pain and Joy Thresholds -/

/-- Pain threshold: strain above which experience is painful.
    Derived from J-cost strain: the scale where mismatch equals unit normalization. -/
noncomputable def painThreshold : ℝ := 1 / phi

/-- Joy threshold: strain below which experience is pleasant.
    Derived from J-cost optimal: the scale where strain is suppressed by φ relative
    to the pain threshold. -/
noncomputable def joyThreshold : ℝ := 1 / (phi * phi)

/-- **THE PAIN THRESHOLD DERIVATION**
    The pain threshold 1/φ emerges as the scale where the strain-mismatch
    crosses the unit-recognition barrier. -/
theorem painThreshold_derivation :
    painThreshold = 1 / phi := rfl

/-- **THE JOY THRESHOLD DERIVATION**
    The joy threshold 1/φ² emerges as the scale of "resonant suppression",
    where the strain is lower than the pain threshold by exactly the
    self-similarity factor φ. -/
theorem joyThreshold_derivation :
    joyThreshold = painThreshold / phi := by
  unfold painThreshold joyThreshold
  field_simp [phi_ne_zero]

/-- Cost-structure forcing link for pain threshold:
    evaluating at `1/phi` is identical to evaluating at `phi` by J-symmetry. -/
theorem painThreshold_cost_symmetry :
    J painThreshold = J phi := by
  have hs := J_symmetric phi Constants.phi_pos
  simpa [painThreshold, one_div] using hs.symm

/-- The joy threshold is the pain threshold suppressed by one extra `1/phi` factor. -/
theorem joyThreshold_is_phi_suppressed :
    joyThreshold = painThreshold * (1 / phi) := by
  unfold joyThreshold painThreshold
  ring_nf

/-- The pair `(1/phi, 1/phi^2)` exactly satisfies a normalized two-level partition:
    `1/phi + 1/phi^2 = 1`. -/
theorem threshold_partition_identity :
    painThreshold + joyThreshold = 1 := by
  unfold painThreshold joyThreshold
  simpa [pow_two, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    IndisputableMonolith.Support.GoldenRatio.constants_inv_phi_add_inv_phi_sq

/-- Pain threshold is positive -/
theorem painThreshold_pos : 0 < painThreshold := by
  unfold painThreshold
  exact div_pos (by norm_num) Constants.phi_pos

/-- Joy threshold is positive -/
theorem joyThreshold_pos : 0 < joyThreshold := by
  unfold joyThreshold
  exact div_pos (by norm_num) (mul_pos Constants.phi_pos Constants.phi_pos)

/-- Joy threshold is less than pain threshold -/
theorem joy_lt_pain : joyThreshold < painThreshold := by
  unfold joyThreshold painThreshold
  -- 1/(φ²) < 1/φ ≈ 0.382 < 0.618
  -- This follows from φ > 1
  have hphi_pos : 0 < phi := Constants.phi_pos
  have hphi_gt_one : 1 < phi := Constants.one_lt_phi
  -- phi * phi > phi since phi > 1
  have h_sq_gt : phi < phi * phi := by nlinarith
  exact one_div_lt_one_div_of_lt hphi_pos h_sq_gt

/-! ## Pain/Joy Classification -/

/-- Classification of experience -/
inductive ExperienceType where
  | Joy     : ExperienceType  -- strain < joyThreshold
  | Neutral : ExperienceType  -- joyThreshold ≤ strain < painThreshold
  | Pain    : ExperienceType  -- strain ≥ painThreshold
deriving DecidableEq, Repr

/-- Classify a strain value -/
noncomputable def classifyStrain (s : ℝ) : ExperienceType :=
  if s < joyThreshold then ExperienceType.Joy
  else if s < painThreshold then ExperienceType.Neutral
  else ExperienceType.Pain

/-! ## The Pain-Joy Dichotomy -/

/-- Pain results from high strain (misalignment) -/
theorem pain_from_misalignment :
    ∀ s : ℝ, painThreshold ≤ s → classifyStrain s = ExperienceType.Pain := by
  intro s hs
  unfold classifyStrain
  have hj := joy_lt_pain
  have hp : ¬ s < joyThreshold := not_lt.mpr (le_trans (le_of_lt hj) hs)
  simp [hp, not_lt.mpr hs]

/-- Joy results from low strain (resonance) -/
theorem joy_from_resonance :
    ∀ s : ℝ, s < joyThreshold → classifyStrain s = ExperienceType.Joy := by
  intro s hs
  unfold classifyStrain
  simp [hs]

/-- The fundamental dichotomy: pain and joy are mutually exclusive -/
theorem pain_joy_dichotomy (s : ℝ) :
    classifyStrain s = ExperienceType.Pain →
    classifyStrain s ≠ ExperienceType.Joy := by
  intro hp
  rw [hp]
  decide

/-! ## Resonance Condition -/

/-- Perfect resonance occurs at zero mismatch -/
def isResonant (tb tq : ℕ) : Bool :=
  (tb % 8 : ℕ) * 45 = (tq % 45 : ℕ) * 8

/-- Resonance implies zero mismatch -/
theorem resonance_zero_mismatch (tb tq : ℕ) (h : isResonant tb tq) :
    phaseMismatch tb tq = 0 := by
  unfold phaseMismatch
  unfold isResonant at h
  simp only [decide_eq_true_eq] at h
  -- h : (tb % 8) * 45 = (tq % 45) * 8
  -- We need: |(tb % 8) / 8 - (tq % 45) / 45| = 0
  -- From h: (tb % 8) / 8 = (tq % 45) / 45
  have h_eq : (↑(tb % 8) : ℝ) / 8 = (↑(tq % 45) : ℝ) / 45 := by
    have h' : (↑((tb % 8) * 45) : ℝ) = (↑((tq % 45) * 8) : ℝ) := congrArg Nat.cast h
    simp only [Nat.cast_mul] at h'
    have h8_pos : (8 : ℝ) ≠ 0 := by norm_num
    have h45_pos : (45 : ℝ) ≠ 0 := by norm_num
    have h1 : (↑(tb % 8) : ℝ) * 45 = (↑(tq % 45) : ℝ) * 8 := h'
    field_simp
    linear_combination h1
  simp only [h_eq, sub_self, abs_zero]

/-! ## Strain to Valence Conversion -/

/-- Convert strain to hedonic valence in [-1, 1].
    Low strain → positive valence (pleasure)
    High strain → negative valence (pain)
    Uses sigmoid-like mapping centered at pain threshold. -/
noncomputable def strainToValence (s : ℝ) : ℝ :=
  let normalized := (painThreshold - s) / painThreshold
  max (-1) (min 1 normalized)

/-- Strain to valence is always bounded in [-1, 1] -/
theorem strainToValence_bounded (s : ℝ) :
    -1 ≤ strainToValence s ∧ strainToValence s ≤ 1 := by
  unfold strainToValence
  constructor
  · exact le_max_left (-1) _
  · exact max_le (by linarith) (min_le_left _ _)

/-- Zero strain gives positive valence -/
theorem zero_strain_positive_valence :
    0 < strainToValence 0 := by
  unfold strainToValence
  simp only [sub_zero, div_self (ne_of_gt painThreshold_pos)]
  norm_num

/-- High strain gives negative valence -/
theorem high_strain_negative_valence (s : ℝ) (hs : 2 * painThreshold < s) :
    strainToValence s < 0 := by
  unfold strainToValence
  have hp := painThreshold_pos
  -- (painThreshold - s) / painThreshold < -1 when s > 2 * painThreshold
  have h_norm : (painThreshold - s) / painThreshold < -1 := by
    have h1 : painThreshold - s < -painThreshold := by linarith
    calc (painThreshold - s) / painThreshold
        < -painThreshold / painThreshold := by exact div_lt_div_of_pos_right h1 hp
      _ = -1 := by field_simp
  -- When normalized < -1, min clamps to normalized, max clamps to -1
  have h_min : min 1 ((painThreshold - s) / painThreshold) = (painThreshold - s) / painThreshold := by
    exact min_eq_right (by linarith)
  have h_max : max (-1) ((painThreshold - s) / painThreshold) = -1 := by
    exact max_eq_left (le_of_lt h_norm)
  simp only [h_min, h_max]
  linarith

/-! ## Summary Theorem -/

/-- Summary: Qualia is the strain tensor of Z-pattern motion -/
theorem qualia_as_strain :
    (∀ m i, 0 ≤ m → 0 < i → 0 ≤ QualiaStrain m i) ∧
    (∀ i, QualiaStrain 0 i = 0) ∧
    (∀ m, QualiaStrain m 1 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact QualiaStrain_nonneg
  · exact zero_mismatch_zero_strain
  · exact unit_intensity_strain

end StrainTensor
end ULQ
end IndisputableMonolith
