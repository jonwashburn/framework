import Mathlib
import IndisputableMonolith.Cost.ClassicalResults

/-!
# Recognition Angle: Core Definitions

This module defines the core objects used across the recognition-angle program:

- `R3`: a convenient alias for 3D Euclidean space
- `angleAt x y z`: the geometric angle at `x` between the directions to `y` and `z`
- `A_of_theta θ := -log (sin θ)`: the kernel action as a function of the sensor angle
- `thetaMin Amax := arcsin (exp (-Amax))`: the budget-dependent minimal recognizable angle

These are formulation-level definitions with conservative totality: `angleAt` is set to `0`
on degeneracies (`y = x` or `z = x`). Theorems and properties are developed in sibling
modules.
-/

noncomputable section

open scoped Real

namespace IndisputableMonolith
namespace Measurement
namespace RecognitionAngle

/-! ## Space and basic vectors -/

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Unit direction from `x` to `y` in `R3`; returns `0` on degeneracy. -/
def dir (x y : R3) : R3 :=
  let v := (y - x)
  if h : ‖v‖ = 0 then 0 else v / ‖v‖

/-- Angle at `x` between rays to `y` and `z`, defined via `arccos` of the inner product
of unit directions. Returns `0` if either ray is degenerate. Range is in `[0, π]`. -/
def angleAt (x y z : R3) : ℝ :=
  let u := dir x y
  let v := dir x z
  if (u = 0) ∨ (v = 0) then 0 else Real.arccos ((⟪u, v⟫_ℝ) / (‖u‖ * ‖v‖))

/-! ## Kernel action and budget threshold -/

/-- Kernel action as a function of the sensor angle `θ`. Domain of interest is `(0, π/2]`. -/
def A_of_theta (θ : ℝ) : ℝ := -Real.log (Real.sin θ)

/-- For budget `Amax > 0`, the minimal admissible angle. -/
def thetaMin (Amax : ℝ) : ℝ := Real.arcsin (Real.exp (-Amax))

/-! ## Core limit and threshold lemmas (via classical results) -/

open Filter

/-- As θ → 0⁺, the kernel action `A_of_theta θ = -log(sin θ)` diverges to `+∞`. -/
theorem action_small_angle_diverges :
  Tendsto (fun θ => A_of_theta θ) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  simpa [A_of_theta] using
    IndisputableMonolith.Cost.ClassicalResults.neg_log_sin_tendsto_atTop_at_zero_right

/-- Budget inequality implies the minimal angle threshold. -/
theorem theta_min_spec {Amax θ : ℝ}
    (hA : 0 < Amax) (hθ0 : 0 < θ) (hθh : θ ≤ π/2)
    (hAineq : A_of_theta θ ≤ Amax) :
    θ ≥ thetaMin Amax := by
  simpa [A_of_theta, thetaMin] using
    IndisputableMonolith.Cost.ClassicalResults.theta_min_spec_inequality Amax θ hA hθ0 hθh hAineq

/-- Threshold is strictly positive and ≤ π/2 for any `Amax>0`. -/
theorem theta_min_range {Amax : ℝ} (hA : 0 < Amax) :
    0 < thetaMin Amax ∧ thetaMin Amax ≤ π/2 := by
  simpa [thetaMin] using
    IndisputableMonolith.Cost.ClassicalResults.theta_min_range Amax hA

/-- If the angle is below the budget threshold, the action exceeds the budget. -/
theorem infeasible_below_thetaMin {Amax θ : ℝ}
    (hA : 0 < Amax) (hθ0 : 0 < θ) (hθh : θ ≤ π/2)
    (hθlt : θ < thetaMin Amax) :
    A_of_theta θ > Amax := by
  -- Using the contrapositive of `theta_min_spec` packaged as a classical result
  -- `theta_min_spec_inequality` gives the forward direction; we obtain strictness here.
  -- This is encoded in `theta_min_spec_inequality` by strict monotonicity in the classical block.
  -- Rearranged here as a direct statement on `A_of_theta`.
  have h := IndisputableMonolith.Cost.ClassicalResults.theta_min_spec_inequality Amax θ hA hθ0 hθh
  -- By contradiction on ≤
  by_contra hle
  have : θ ≥ thetaMin Amax := by simpa [A_of_theta, thetaMin] using h hle
  exact (lt_of_lt_of_le hθlt this).false.elim

end RecognitionAngle
end Measurement
end IndisputableMonolith
