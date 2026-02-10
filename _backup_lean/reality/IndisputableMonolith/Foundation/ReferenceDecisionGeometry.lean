import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.Reference

/-!
# Reference Decision Geometry (Finite Dictionaries)

This module mechanizes the core “decision-geometry” result from the aboutness / meaning
framework: for the canonical reciprocal cost

`J(x) = (x + 1/x)/2 - 1`,

the preference boundary between two object scales `y₁ < y₂` occurs at the geometric mean:

`x² = y₁ * y₂`.

This is the kernel lemma behind the finite-dictionary boundary theorem in the paper
`papers/Algebra_of_Aboutness_Amir_final-vv.tex` (geometric-mean decision boundaries).

Lean module: `IndisputableMonolith.Foundation.ReferenceDecisionGeometry`
-/

namespace IndisputableMonolith
namespace Foundation
namespace ReferenceDecisionGeometry

open Real
open scoped BigOperators

/-! ## Part 1: A closed-form for ratio-cost -/

lemma Jcost_div_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Cost.Jcost (x / y) = (x - y) ^ 2 / (2 * x * y) := by
  -- J(x/y) = ((x/y) + (y/x))/2 - 1 = (x^2 + y^2 - 2xy) / (2xy) = (x-y)^2/(2xy)
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : y ≠ 0 := hy.ne'
  unfold Cost.Jcost
  -- clear denominators
  field_simp [hx0, hy0]
  ring

/-! ## Part 2: Two-object boundary at the geometric mean -/

theorem jcost_div_le_iff_sq_le_mul
    {x y₁ y₂ : ℝ} (hx : 0 < x) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (h12 : y₁ < y₂) :
    Cost.Jcost (x / y₁) ≤ Cost.Jcost (x / y₂) ↔ x ^ 2 ≤ y₁ * y₂ := by
  -- Rewrite both sides using the rational form (x-y)^2/(2xy).
  have hJ1 : Cost.Jcost (x / y₁) = (x - y₁) ^ 2 / (2 * x * y₁) :=
    Jcost_div_eq x y₁ hx hy₁
  have hJ2 : Cost.Jcost (x / y₂) = (x - y₂) ^ 2 / (2 * x * y₂) :=
    Jcost_div_eq x y₂ hx hy₂
  rw [hJ1, hJ2]

  have hx0 : x ≠ 0 := hx.ne'
  have hy10 : y₁ ≠ 0 := hy₁.ne'
  have hy20 : y₂ ≠ 0 := hy₂.ne'
  have hmul_pos : 0 < 2 * x * y₁ * y₂ := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    have h2x : 0 < (2 : ℝ) * x := mul_pos h2 hx
    have h2xy₁ : 0 < (2 : ℝ) * x * y₁ := mul_pos h2x hy₁
    have h2xy₁y₂ : 0 < ((2 : ℝ) * x * y₁) * y₂ := mul_pos h2xy₁ hy₂
    simpa [mul_assoc] using h2xy₁y₂

  constructor
  · intro hle
    -- Multiply both sides by a positive denominator to clear fractions.
    have hmul :
        (2 * x * y₁ * y₂) * ((x - y₁) ^ 2 / (2 * x * y₁))
          ≤ (2 * x * y₁ * y₂) * ((x - y₂) ^ 2 / (2 * x * y₂)) := by
      exact mul_le_mul_of_nonneg_left hle (le_of_lt hmul_pos)
    have hsim1 :
        (2 * x * y₁ * y₂) * ((x - y₁) ^ 2 / (2 * x * y₁)) = y₂ * (x - y₁) ^ 2 := by
      field_simp [hx0, hy10]
    have hsim2 :
        (2 * x * y₁ * y₂) * ((x - y₂) ^ 2 / (2 * x * y₂)) = y₁ * (x - y₂) ^ 2 := by
      field_simp [hx0, hy20]
    have hmain : y₂ * (x - y₁) ^ 2 ≤ y₁ * (x - y₂) ^ 2 := by
      simpa [hsim1, hsim2] using hmul
    -- Now solve the resulting polynomial inequality.
    nlinarith [hmain, h12]
  · intro hsq
    -- Build the cleared-denominator inequality directly from x^2 ≤ y₁*y₂.
    have hmain : y₂ * (x - y₁) ^ 2 ≤ y₁ * (x - y₂) ^ 2 := by
      nlinarith [hsq, h12]
    have hsim1 :
        (2 * x * y₁ * y₂) * ((x - y₁) ^ 2 / (2 * x * y₁)) = y₂ * (x - y₁) ^ 2 := by
      field_simp [hx0, hy10]
    have hsim2 :
        (2 * x * y₁ * y₂) * ((x - y₂) ^ 2 / (2 * x * y₂)) = y₁ * (x - y₂) ^ 2 := by
      field_simp [hx0, hy20]
    have hmul :
        (2 * x * y₁ * y₂) * ((x - y₁) ^ 2 / (2 * x * y₁))
          ≤ (2 * x * y₁ * y₂) * ((x - y₂) ^ 2 / (2 * x * y₂)) := by
      simpa [hsim1, hsim2] using hmain
    -- Cancel the positive factor.
    exact le_of_mul_le_mul_left hmul hmul_pos

end ReferenceDecisionGeometry
end Foundation
end IndisputableMonolith
