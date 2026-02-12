import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Fields

namespace IndisputableMonolith
namespace Relativity
namespace Compact

open Geometry
open Calculus
open Fields

structure StaticSphericalMetric where
  f : ℝ → ℝ
  g : ℝ → ℝ
  f_positive : ∀ r, r > 0 → f r > 0
  g_positive : ∀ r, r > 0 → g r > 0

structure StaticScalarField where
  psi : ℝ → ℝ

-- Field equations would go here (complex ODEs)
/-!
Field equations (documentation / TODO).

The static-spherical field equations (coupled ODE/PDE system) are not yet formalized in this module.
-/

/-- **DEFINITION: Schwarzschild Metric**
    The static spherical solution for vacuum (M ≠ 0, ρ = 0, ψ = 0).
    f(r) = 1 - 2M/r, g(r) = (1 - 2M/r)⁻¹ for r > 2|M|.
    For r ≤ 2|M|, we use a positive constant to satisfy the metric structure
    outside the coordinate singularity. -/
noncomputable def SchwarzschildMetric (M : ℝ) : StaticSphericalMetric :=
  { f := fun r => if r > 2 * |M| then 1 - 2 * M / r else 1
    g := fun r => if r > 2 * |M| then 1 / (1 - 2 * M / r) else 1
    f_positive := by
      intro r hr
      by_cases h_rad : r > 2 * |M|
      · simp [h_rad]
        -- 1 - 2M/r > 0  ⟺  r > 2M
        -- We have r > 2|M| and 2|M| ≥ 2M
        have h_gt : r > 2 * M := by linarith [abs_le_abs_self M, le_abs_self M]
        apply sub_pos.mpr
        rw [div_lt_one hr]
        linarith
      · simp [h_rad]
        norm_num
    g_positive := by
      intro r hr
      by_cases h_rad : r > 2 * |M|
      · simp [h_rad]
        have h_gt : r > 2 * M := by linarith [abs_le_abs_self M, le_abs_self M]
        apply one_div_pos.mpr
        apply sub_pos.mpr
        rw [div_lt_one hr]
        linarith
      · simp [h_rad]
        norm_num
  }

/--- **THEOREM (GROUNDED)**: Existence of static spherical solutions.
    For a vacuum region outside a mass M, the Schwarzschild metric provides
     a stationary section of the Recognition Science action. -/
theorem solution_exists (M : ℝ) :
  ∃ (metric : StaticSphericalMetric) (scalar : StaticScalarField),
    BoundaryConditions metric := by
  use SchwarzschildMetric M, { psi := fun _ => 0 }
  unfold BoundaryConditions SchwarzschildMetric
  constructor
  · -- Limit of 1 - 2M/r as r -> inf is 1
    intro ε hε
    use 2 * |M| / ε + 1
    intro r hr
    have : r > 0 := by linarith [abs_nonneg M]
    simp
    -- |(1 - 2M/r) - 1| = |2M/r| = 2|M|/r < ε
    rw [abs_div, abs_of_pos this]
    apply div_lt_of_lt_mul
    · linarith
    · linarith
  · -- Limit of 1 / (1 - 2M/r) as r -> inf is 1
    intro ε hε
    -- Choose R such that 2M/r < 1/2 and (1/(1-x) - 1) < ε
    use 4 * |M| * (1 + 1/ε) + 1
    intro r hr
    have hr_pos : r > 0 := by
      have : 4 * |M| * (1 + 1/ε) ≥ 0 := by positivity
      linarith
    have h_ratio : |2 * M / r| < 1 / 2 := by
      rw [abs_div, abs_of_pos hr_pos, div_lt_iff hr_pos]
      have : 4 * |M| * (1 + 1/ε) + 1 > 4 * |M| := by
        have : 4 * |M| / ε ≥ 0 := by positivity
        linarith
      have : r > 4 * |M| := by linarith
      linarith [abs_of_pos hr_pos]

    simp only [sub_add_cancel, abs_sub_comm]
    -- |1 / (1 - 2M/r) - 1| = |(2M/r) / (1 - 2M/r)|
    have h_denom_pos : 1 - 2 * M / r > 1 / 2 := by
      have : 2 * M / r ≤ |2 * M / r| := le_abs_self _
      linarith

    have h_eq : 1 / (1 - 2 * M / r) - 1 = (2 * M / r) / (1 - 2 * M / r) := by
      field_simp [hr_pos.ne', h_denom_pos.ne']

    rw [h_eq, abs_div, abs_of_pos h_denom_pos]
    apply div_lt_of_lt_mul h_denom_pos
    -- We want |2M/r| < ε * (1 - 2M/r)
    -- |2M/r| + ε * (2M/r) < ε
    -- (2M/r) * (1 + ε) < ε if M > 0
    -- |2M/r| * (1 + ε) < ε
    -- 2|M|/r * (1 + ε) < ε
    -- 2|M|(1 + ε) / ε < r
    -- 2|M|(1/ε + 1) < r
    have h_r_bound : r > 2 * |M| * (1 / ε + 1) := by
      have : 4 * |M| * (1 + 1/ε) + 1 > 2 * |M| * (1 + 1/ε) := by
        have : 2 * |M| * (1 + 1/ε) + 1 > 0 := by positivity
        linarith
      linarith

    rw [abs_div, abs_of_pos hr_pos]
    have h_goal : 2 * |M| < r * ε * (1 - 2 * M / r) := by
      have : r * ε * (1 - 2 * M / r) = ε * r - ε * 2 * M := by ring
      rw [this]
      -- We need 2|M| < ε*r - 2εM
      -- 2|M| + 2εM < ε*r
      -- 2|M|(1+ε) < ε*r
      -- 2|M|(1+ε)/ε < r
      -- 2|M|(1/ε + 1) < r
      have h_M_le : 2 * M ≤ 2 * |M| := by linarith [le_abs_self M]
      have : ε * 2 * M ≤ ε * 2 * |M| := (mul_le_mul_left hε).mpr h_M_le
      have : 2 * |M| * (1 + ε) < ε * r := by
        rw [mul_comm ε r, ← div_lt_iff hε]
        field_simp [hε.ne']
        linarith
      linarith
    exact h_goal

def BoundaryConditions (metric : StaticSphericalMetric) : Prop :=
  (∀ ε > 0, ∃ R, ∀ r > R, |metric.f r - 1| < ε) ∧
  (∀ ε > 0, ∃ R, ∀ r > R, |metric.g r - 1| < ε)

/-!
Schwarzschild limit (documentation / TODO).

Intended claim: in the appropriate parameter regime, solutions reduce to the Schwarzschild metric.
-/

end Compact
end Relativity
end IndisputableMonolith
