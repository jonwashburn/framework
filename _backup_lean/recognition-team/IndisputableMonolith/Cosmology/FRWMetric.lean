import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

open Geometry
open Calculus

structure ScaleFactor where
  a : ℝ → ℝ
  a_positive : ∀ t, 0 < a t

noncomputable def metric_FRW (scale : ScaleFactor) : MetricTensor where
  g := fun x _ low =>
    let μ := low 0
    let ν := low 1
    let t := x 0
    if μ = 0 ∧ ν = 0 then -1
    else if μ = ν ∧ μ.val > 0 then (scale.a t)^2
    else 0
  symmetric := by
    intro x μ ν
    simp only []
    -- Case analysis on the if-then-else structure
    by_cases h1 : μ = 0 ∧ ν = 0
    · by_cases h2 : ν = 0 ∧ μ = 0
      · rfl
      · simp [h1, h2]
    · by_cases h2 : μ = ν ∧ μ.val > 0
      · by_cases h3 : ν = μ ∧ ν.val > 0
        · rfl
        · cases h2; cases h3; simp_all
      · by_cases h3 : ν = μ ∧ ν.val > 0
        · cases h2; cases h3; simp_all
        · rfl

noncomputable def christoffel_FRW (scale : ScaleFactor) (t : ℝ) (μ ρ σ : Fin 4) : ℝ :=
  let H := deriv scale.a t / scale.a t
  if μ = 0 ∧ ρ.val > 0 ∧ σ.val > 0 ∧ ρ = σ then
    H * (scale.a t)^2
  else if μ.val > 0 ∧ ρ = 0 ∧ σ = μ then H
  else if μ.val > 0 ∧ ρ = μ ∧ σ = 0 then H
  else 0

/-!
Christoffel symbols for FRW (documentation / TODO).

Intended claim: `christoffel_FRW` matches the standard FRW Christoffel symbols.
-/

noncomputable def ricci_FRW_00 (scale : ScaleFactor) (t : ℝ) : ℝ :=
  -3 * deriv (deriv scale.a) t / scale.a t

noncomputable def ricci_FRW_ij (scale : ScaleFactor) (t : ℝ) : ℝ :=
  let H := deriv scale.a t / scale.a t
  let a_ddot := deriv (deriv scale.a) t
  (scale.a t)^2 * (a_ddot / scale.a t + 2 * H^2)

/-!
Ricci tensor formulas for FRW (documentation / TODO).

Intended claim: `ricci_FRW_00` and `ricci_FRW_ij` match the standard FRW Ricci components.
-/

end Cosmology
end Relativity
end IndisputableMonolith
