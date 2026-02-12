import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.ConstMulAction

noncomputable section

open Classical MeasureTheory
open scoped Convolution

namespace Hodge.GMT

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [HasContDiffBump E]

/-- Base bump function on `E`. -/
def bumpBase : ContDiffBump (0 : E) :=
  { rIn := 1
    rOut := 2
    rIn_pos := Real.zero_lt_one
    rIn_lt_rOut := by norm_num }

/-- The underlying bump function as a map `E → ℝ`. -/
def bumpBaseFun : E → ℝ :=
  ContDiffBump.toFun (c := (0 : E)) (bumpBase (E := E))

/-- Standard bump function on `E`, scaled by ε. -/
def bump (ε : ℝ) (x : E) : ℝ :=
  bumpBaseFun (E := E) (ε⁻¹ • x)

/-- Shifted bump function: `y ↦ ρ_ε(x - y)`. -/
def shifted_bump (ε : ℝ) (x : E) (y : E) : ℝ :=
  bump ε (x - y)

/-- Euclidean mollifier (convolution with a bump). -/
def mollifyFunction (ε : ℝ) (f : E → ℝ) : E → ℝ :=
  fun x => ∫ y, bump ε (x - y) * f y ∂volume

/-- Smoothness of the Euclidean mollifier. -/
theorem mollifyFunction_contDiff (ε : ℝ) (f : E → ℝ) (hε : ε ≠ 0)
    (hf : LocallyIntegrable f (volume : Measure E)) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyFunction ε f) := by
  have hcompact : HasCompactSupport (fun x => bump (E := E) ε x) := by
    have hbase : HasCompactSupport (fun x => bumpBaseFun (E := E) x) := by
      simpa [bumpBaseFun] using (bumpBase (E := E)).hasCompactSupport
    simpa [bump] using hbase.comp_smul (inv_ne_zero hε)
  have hcont : ContDiff ℝ (⊤ : ℕ∞) (fun x => bump (E := E) ε x) := by
    -- `ContDiffBump` is smooth, and scaling is smooth.
    have hbase : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => bumpBaseFun (E := E) x) := by
      simpa [bumpBaseFun] using (bumpBase (E := E)).contDiff (n := (⊤ : ℕ∞))
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x : E => ε⁻¹ • x) :=
      (contDiff_const_smul (c := ε⁻¹)).comp contDiff_id
    simpa [bump] using hbase.comp hg
  have hconv :
      ContDiff ℝ (⊤ : ℕ∞)
        (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] fun x => bump (E := E) ε x) :=
    hcompact.contDiff_convolution_right (n := (⊤ : ℕ∞)) (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure E)) hf hcont
  have hmollify :
      mollifyFunction (E := E) ε f =
        (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] fun x => bump (E := E) ε x) := by
    funext x
    simp [mollifyFunction, convolution_lsmul, smul_eq_mul, mul_comm]
  simpa [hmollify] using hconv

end Local

end Hodge.GMT
