import Mathlib
import IndisputableMonolith.MusicTheory.HarmonicModes
import IndisputableMonolith.Foundation.PhiForcing

/-!
# Consonance: J-Cost of Musical Intervals

This module derives **musical consonance and dissonance from J-cost**.

## Core Principle

In Recognition Science, the J-cost function J(x) = ½(x + 1/x) - 1 measures
the "recognition cost" of a configuration ratio. For musical intervals:

- **Consonance**: Low J-cost → harmonics align → sounds "pleasant"
- **Dissonance**: High J-cost → harmonics clash → sounds "tense"

## The Consonance Hierarchy

| Interval | Ratio | J-Cost | Classification |
|----------|-------|--------|----------------|
| Unison | 1:1 | 0 | Perfect consonance |
| Octave | 2:1 | 0.25 | Perfect consonance |
| Fifth | 3:2 | ~0.083 | Perfect consonance |
| Fourth | 4:3 | ~0.042 | Perfect consonance |
| Major Third | 5:4 | ~0.025 | Imperfect consonance |
| Minor Third | 6:5 | ~0.017 | Imperfect consonance |
| Tritone | √2:1 | ~0.207 | Dissonance |
| Minor Second | 16:15 | ~0.0003 | Dissonance (by complexity) |

The smaller the J-cost, the more consonant the interval—with a correction for
complexity (the sum of numerator and denominator in the ratio).

-/

namespace IndisputableMonolith
namespace MusicTheory
namespace Consonance

open Real HarmonicModes

/-! ## J-Cost for Intervals -/

/-- J-cost of a frequency ratio (from HarmonicModes). -/
noncomputable def intervalCost (ratio : ℝ) : ℝ := J ratio

/-- Complexity of a rational interval p/q: p + q.
    Higher complexity = more "distant" in harmonic space. -/
def rationalComplexity (p q : ℕ) : ℕ := p + q

/-- Combined consonance measure: penalizes both J-cost and complexity.
    consonance(p/q) = 1 / (1 + J(p/q) + (p+q)/100)
    Higher value = more consonant. -/
noncomputable def consonanceScore (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) : ℝ :=
  1 / (1 + intervalCost ((p : ℝ) / q) + (rationalComplexity p q : ℝ) / 100)

/-! ## The Consonance Ordering -/

/-- Unison (1:1) has zero J-cost—perfect consonance. -/
theorem unison_zero_cost : intervalCost 1 = 0 := J_one

/-- The octave (2:1) is consonant with J-cost = 1/4. -/
theorem octave_cost : intervalCost 2 = 1/4 := J_two

/-- The perfect fifth (3:2) has J-cost = 1/12. -/
theorem fifth_cost : intervalCost (3/2) = 1/12 := J_three_halves

/-- The perfect fourth (4:3) has J-cost.
    J(4/3) = ½(4/3 + 3/4) - 1 = ½(16/12 + 9/12) - 1 = ½(25/12) - 1 = 25/24 - 1 = 1/24 -/
theorem fourth_cost : intervalCost (4/3) = 1/24 := by
  simp only [intervalCost, J]
  norm_num

/-- The major third (5:4) has J-cost = 1/40. -/
theorem major_third_cost : intervalCost (5/4) = 1/40 := by
  simp only [intervalCost, J]
  norm_num

/-- The minor third (6:5) has J-cost = 1/60. -/
theorem minor_third_cost : intervalCost (6/5) = 1/60 := by
  simp only [intervalCost, J]
  norm_num

/-! ## Consonance Hierarchy Theorems -/

/-- Perfect unison is the most consonant interval. -/
theorem unison_most_consonant :
    ∀ x : ℝ, x ≠ 1 → x > 0 → intervalCost 1 < intervalCost x := by
  intro x hx1 hxpos
  rw [unison_zero_cost]
  simp only [intervalCost, J]
  have hsq : (x - 1)^2 > 0 := by
    have hne : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    exact sq_pos_of_ne_zero hne
  have h : x + x⁻¹ > 2 := by
    have hdiv_pos : (x - 1)^2 / x > 0 := div_pos hsq hxpos
    have : (x - 1)^2 / x = x - 2 + x⁻¹ := by field_simp; ring
    linarith
  linarith

/-- The fifth is more consonant than the octave (lower J-cost). -/
theorem fifth_more_consonant_than_octave :
    intervalCost (3/2) < intervalCost 2 := J_fifth_lt_J_octave

/-- The fourth is more consonant than the fifth. -/
theorem fourth_more_consonant_than_fifth :
    intervalCost (4/3) < intervalCost (3/2) := by
  rw [fourth_cost, fifth_cost]
  norm_num

/-- The major third is more consonant than the fourth. -/
theorem major_third_more_consonant_than_fourth :
    intervalCost (5/4) < intervalCost (4/3) := by
  rw [major_third_cost, fourth_cost]
  norm_num

/-- The minor third is more consonant than the major third. -/
theorem minor_third_more_consonant_than_major_third :
    intervalCost (6/5) < intervalCost (5/4) := by
  rw [minor_third_cost, major_third_cost]
  norm_num

/-! ## The Complete Consonance Ordering

For superparticular ratios (n+1)/n, J-cost decreases as n increases:
J((n+1)/n) = 1/(2n(n+1))

This gives the hierarchy:
2/1 > 3/2 > 4/3 > 5/4 > 6/5 > ...

But complexity also matters! The minor second 16/15 has very low J-cost
but high complexity, making it dissonant in practice.
-/

/-- J-cost of superparticular ratio (n+1)/n. -/
theorem superparticular_cost (n : ℕ) (hn : 0 < n) :
    intervalCost ((n + 1 : ℝ) / n) = 1 / (2 * n * (n + 1)) := by
  simp only [intervalCost, J]
  have hn' : (n : ℝ) ≠ 0 := by norm_cast; linarith
  field_simp
  ring

/-- Superparticular ratios become more consonant as n increases. -/
theorem superparticular_consonance_increases (n : ℕ) (hn : 0 < n) :
    intervalCost ((n + 2 : ℝ) / (n + 1)) < intervalCost ((n + 1 : ℝ) / n) := by
  have h_rhs : intervalCost ((n + 1 : ℝ) / n) = 1 / (2 * n * (n + 1)) := superparticular_cost n hn
  have hn1 : 0 < n + 1 := by linarith
  have h_lhs : intervalCost ((n + 2 : ℝ) / (n + 1)) = 1 / (2 * (n + 1) * (n + 2)) := by
    have : (n + 2 : ℝ) = (n + 1 : ℕ) + 1 := by norm_cast
    rw [this]
    exact_mod_cast superparticular_cost (n + 1) hn1
  rw [h_lhs, h_rhs]
  apply one_div_lt_one_div_of_lt
  · positivity
  · calc 2 * (n : ℝ) * (n + 1) = (2 * (n + 1)) * n := by ring
      _ < (2 * (n + 1)) * (n + 2) := by
        apply mul_lt_mul_of_pos_left
        · norm_cast; linarith
        · positivity
      _ = 2 * (n + 1) * (n + 2) := by ring

/-! ## Dissonance: High J-Cost Intervals -/

/-- The tritone (√2 : 1) has J-cost ≈ 0.207. -/
noncomputable def tritone_ratio : ℝ := Real.sqrt 2

theorem tritone_cost_positive : 0 < intervalCost tritone_ratio := by
  -- tritone_ratio = √2, and J(√2) > 0 since √2 ≠ 1
  unfold intervalCost tritone_ratio
  simp only [J]
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt2_neq_1 : Real.sqrt 2 ≠ 1 := by
    intro h
    have : (Real.sqrt 2)^2 = 1^2 := by rw [h]
    rw [Real.sq_sqrt (by norm_num)] at this
    norm_num at this
  -- (x + 1/x)/2 - 1 > 0  <=> x + 1/x > 2
  -- (x-1)^2 / (2x) > 0
  have : (Real.sqrt 2 + (Real.sqrt 2)⁻¹) / 2 - 1 = (Real.sqrt 2 - 1)^2 / (2 * Real.sqrt 2) := by
    field_simp [h_sqrt2_pos.ne']
    ring
  rw [this]
  apply div_pos
  · exact sq_pos_of_ne_zero (sub_ne_zero.mpr h_sqrt2_neq_1)
  · positivity

/-- The tritone is actually MORE consonant than the octave by pure J-cost! -/
theorem tritone_more_consonant_than_octave_by_j_cost :
    intervalCost tritone_ratio < intervalCost 2 := by
  unfold intervalCost tritone_ratio
  simp only [J]
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt2_ne_zero : Real.sqrt 2 ≠ 0 := h_sqrt2_pos.ne'
  have h_inv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    rw [inv_eq_one_div, div_eq_div_iff h_sqrt2_ne_zero (by norm_num : (2:ℝ) ≠ 0)]
    rw [← sq, Real.sq_sqrt (by norm_num)]
    ring
  have h_sum : Real.sqrt 2 + (Real.sqrt 2)⁻¹ = (3 * Real.sqrt 2) / 2 := by
    rw [h_inv]
    ring
  have h_val : 3 * Real.sqrt 2 < 5 := by
    have h18 : 3 * Real.sqrt 2 = Real.sqrt 18 := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3), ← Real.sqrt_mul (by norm_num)]
      norm_num
    have h25 : (5 : ℝ) = Real.sqrt 25 := by
      rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
      norm_num
    rw [h18, h25]
    apply Real.sqrt_lt_sqrt (by norm_num)
    norm_num
  simp only [sub_lt_sub_iff_right]
  -- Goal: (Real.sqrt 2 + (Real.sqrt 2)⁻¹) / 2 < (2 + 2⁻¹) / 2
  calc (Real.sqrt 2 + (Real.sqrt 2)⁻¹) / 2
      = ((3 * Real.sqrt 2) / 2) / 2 := by rw [h_sum]
    _ = (3 * Real.sqrt 2) / 4 := by ring
    _ < 5 / 4 := by
      rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]
      linarith
    _ = (2 + (2 : ℝ)⁻¹) / 2 := by norm_num

/-! ## Consonance Predicates -/

/-- An interval is "consonant" if its J-cost is below a threshold.
    We use 1/4 (the octave) as the boundary. -/
def isConsonant (ratio : ℝ) : Prop := intervalCost ratio ≤ 1/4

/-- An interval is "perfectly consonant" if its J-cost is very low.
    We use 1/10 as the threshold. -/
def isPerfectlyConsonant (ratio : ℝ) : Prop := intervalCost ratio ≤ 1/10

/-- An interval is "dissonant" if its J-cost exceeds the octave threshold. -/
def isDissonant (ratio : ℝ) : Prop := intervalCost ratio > 1/4

/-- Unison is perfectly consonant. -/
theorem unison_perfectly_consonant : isPerfectlyConsonant 1 := by
  simp [isPerfectlyConsonant, unison_zero_cost]

/-- The fifth is perfectly consonant. -/
theorem fifth_perfectly_consonant : isPerfectlyConsonant (3/2) := by
  simp [isPerfectlyConsonant, fifth_cost]
  norm_num

/-- The octave is consonant (at the boundary). -/
theorem octave_consonant : isConsonant 2 := by
  simp [isConsonant, octave_cost]

/-! ## Mode-Based Consonance -/

/-- Distance between two phases in the 8-cycle. -/
def phaseDistance (i j : HarmonicPhase) : ℕ :=
  min (((j : ℕ) + 8 - (i : ℕ)) % 8) (((i : ℕ) + 8 - (j : ℕ)) % 8)

/-- Phases 0 apart (unison) are perfectly consonant. -/
theorem phase_zero_consonant (i : HarmonicPhase) :
    phaseDistance i i = 0 := by simp [phaseDistance]

/-- Phases 4 apart (tritone/midpoint) form the symmetric axis. -/
theorem phase_four_symmetric (i : HarmonicPhase) :
    phaseDistance i (i + 4) = 4 := by
  unfold phaseDistance
  -- i + 4 in Fin 8 is (i.val + 4) % 8
  set j := i + 4
  have hj : j.val = (i.val + 4) % 8 := rfl
  have h1 : (j.val + 8 - i.val) % 8 = 4 := by
    rw [hj]
    fin_cases i <;> simp
  have h2 : (i.val + 8 - j.val) % 8 = 4 := by
    rw [hj]
    fin_cases i <;> simp
  rw [h1, h2, min_self]

end Consonance
end MusicTheory
end IndisputableMonolith
