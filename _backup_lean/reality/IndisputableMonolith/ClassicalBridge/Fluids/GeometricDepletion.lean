/-
Geometric Depletion: Constantin-Fefferman Mechanism
====================================================

This file contains the core geometric depletion results that enable the
Recognition Science approach to Navier-Stokes regularity.

Key insight: When vorticity is aligned within angle π/6, the stretching
term is significantly reduced (depleted) due to cancellation in the
Biot-Savart integral.

Ported from github.com/jonwashburn/navier-stokes-lean
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Module.Basic
import IndisputableMonolith.ClassicalBridge.Fluids.BasicDefinitions

namespace IndisputableMonolith.ClassicalBridge.Fluids

open Real

/-!
## Biot-Savart Kernel
-/

/-- A minimal singular kernel structure for our purposes -/
structure SingularKernel (X Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  kernel : X → X → (Y → Y)
  bound : ℝ → ℝ  -- bound(r) gives the L¹ bound outside ball of radius r

/-- Biot–Savart kernel in R³. K(x,y) = (x-y) × I / (4π|x-y|³) -/
noncomputable def BS_kernel : SingularKernel (Fin 3 → ℝ) (Fin 3 → ℝ) :=
  { kernel := fun x y v =>
      if _h : x = y then 0 else
      let r := x - y
      let norm_r := ‖r‖
      -- Cross product (x-y) × v divided by 4π|x-y|³
      (1 / (4 * π * norm_r^3)) • ![
        r 1 * v 2 - r 2 * v 1,
        r 2 * v 0 - r 0 * v 2,
        r 0 * v 1 - r 1 * v 0
      ]
    bound := fun r => 3 / (4 * π * r) }

/-!
## Kernel Bounds (TODO)
-/

-- The Biot–Savart kernel bounds, far-field estimates, and the Constantin–Fefferman
-- near-field cancellation mechanism are not yet formalized here.
--
-- When we need them, we should either:
-- - prove them using Mathlib's analysis/harmonic-analysis infrastructure, or
-- - package them as explicit `...Hypothesis` structures (not `axiom`).

/-!
## Angle Helpers
-/

/-- Angle between vectors (using inner product) -/
noncomputable def angle (v w : Fin 3 → ℝ) : ℝ :=
  if v = 0 then π/2
  else if w = 0 then π/2
  else Real.arccos ((∑ i, v i * w i) / (‖v‖ * ‖w‖))

-- Angle bound implies norm bound (TODO)
-- (TODO) Angle-based inequalities will be added as lemmas once the trigonometric / inner-product
-- estimates are integrated.

-- (TODO) Far-field / near-field decomposition lemmas will live here.

/-!
## Main Geometric Depletion Theorem
-/

/-- Geometric depletion for VectorField type -/
theorem geometric_depletion_vectorfield
    (u : VectorField)
    (x : Fin 3 → ℝ) (r : ℝ)
    (_h_div_free : divergence u = fun _ => 0)
    (_h_smooth : ContDiff ℝ 2 u)
    (hr_pos : r > 0)
    (h_scale : r * supNorm (vorticity u) ≤ 1)
    (h_bdd : BddAbove (Set.range fun y => ‖vorticity u y‖)) :
    ∃ C > 0, ‖vorticity u x‖ ≤ C / r := by
  -- Note: this theorem is currently a **coarse** bound obtained directly from the scale
  -- hypothesis `r * supNorm (vorticity u) ≤ 1` together with the pointwise ≤ supNorm axiom.
  -- A sharper Constantin–Fefferman-style depletion estimate will require the (TODO) kernel bounds.
  refine ⟨(1 : ℝ), by norm_num, ?_⟩
  have h_point : ‖vorticity u x‖ ≤ supNorm (vorticity u) :=
    le_supNorm_apply (vorticity u) x h_bdd
  have h_sup : supNorm (vorticity u) ≤ (1 : ℝ) / r := by
    -- rewrite `r * supNorm ≤ 1` as `supNorm * r ≤ 1` and divide by `r > 0`
    have h_mul : supNorm (vorticity u) * r ≤ 1 := by
      simpa [mul_comm] using h_scale
    exact (le_div_iff₀ hr_pos).2 h_mul
  exact le_trans h_point h_sup

/-!
## Vorticity Controls Gradient
-/

/-- Hypothesis packaging the (classical) Calderón–Zygmund estimate used in the bridge.

This is the analytic input that controls the velocity gradient by the vorticity for
divergence-free vector fields.  We keep it explicit (rather than `sorry`) so downstream
theorems can state precisely what they depend on.
-/
structure VorticityControlsGradientHypothesis (u : VectorField) : Prop where
  /-- Divergence-free condition (incompressibility) -/
  div_free : divergence u = fun _ => 0
  /-- Smoothness assumption ensuring the expressions make sense -/
  smooth : ContDiff ℝ 1 u
  /-- Calderón–Zygmund-type pointwise control of the gradient by curl/vorticity -/
  bound : ∀ x : Fin 3 → ℝ, gradientNormSquared u x ≤ C_CZ * ‖curl u x‖^2

/-- Vorticity controls the velocity gradient (Calderón-Zygmund theory) -/
theorem vorticity_controls_gradient (u : VectorField)
    (H : VorticityControlsGradientHypothesis u)
    (x : Fin 3 → ℝ) :
    gradientNormSquared u x ≤ C_CZ * ‖curl u x‖^2 := by
  exact H.bound x

end IndisputableMonolith.ClassicalBridge.Fluids
