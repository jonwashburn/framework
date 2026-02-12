import Hodge.Analytic.DistributionTestForms

import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Stage 2 (Euclidean seed): Integration currents from finite measures

This is an **off-proof-track** Stage 2 seed for the plan in
`tex/archive/HodgePlan-mc-28.1.26.rtf`.

For a finite measure `μ` on a Euclidean space `E`, we define the linear functional

`T_μ(φ) = ∫ x, φ x ∂μ`

as a **continuous** linear functional on Mathlib's LF-space of test functions `𝓓(Ω, ℝ)` by
composing existing continuous linear maps:

`𝓓(Ω,ℝ) →L (E →ᵇ ℝ) →L (E →₁[μ] ℝ) →L ℝ`.

This is the measure-theoretic prototype for “integration currents”. Submanifold integration and
Stokes live downstream.
-/

noncomputable section

open scoped Distributions BoundedContinuousFunction ENNReal

namespace Hodge
namespace Analytic
namespace Stage2

open Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable {Ω : TopologicalSpace.Opens E}

/-- The (Euclidean) integration current associated to a finite measure `μ`. -/
noncomputable def integrationCurrent (μ : MeasureTheory.Measure E) [MeasureTheory.IsFiniteMeasure μ] :
    𝓓(Ω, ℝ) →L[ℝ] ℝ :=
  (MeasureTheory.L1.integralCLM (α := E) (E := ℝ) (μ := μ)).comp <|
    (BoundedContinuousFunction.toLp (E := ℝ) (p := (1 : ℝ≥0∞)) μ ℝ).comp <|
      (TestFunction.toBoundedContinuousFunctionCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (F := ℝ) ℝ)

@[simp]
theorem integrationCurrent_apply (μ : MeasureTheory.Measure E) [MeasureTheory.IsFiniteMeasure μ]
    (φ : 𝓓(Ω, ℝ)) :
    integrationCurrent (Ω := Ω) μ φ =
      MeasureTheory.L1.integral
        ((BoundedContinuousFunction.toLp (E := ℝ) (p := (1 : ℝ≥0∞)) μ ℝ)
          ((TestFunction.toBoundedContinuousFunctionCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (F := ℝ) ℝ) φ)) :=
by
  -- `MeasureTheory.L1.integral` is an irreducible definition; use `integral_eq` to rewrite it.
  simpa [integrationCurrent] using
    (MeasureTheory.L1.integral_eq (μ := μ) (E := ℝ) (α := E)
        ((BoundedContinuousFunction.toLp (E := ℝ) (p := (1 : ℝ≥0∞)) μ ℝ)
          ((TestFunction.toBoundedContinuousFunctionCLM (n := (⊤ : ℕ∞)) (Ω := Ω) (F := ℝ) ℝ)
            φ))).symm

end Stage2
end Analytic
end Hodge
