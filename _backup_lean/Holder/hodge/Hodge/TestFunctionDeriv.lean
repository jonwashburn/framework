import Mathlib.Analysis.Distribution.TestFunction

/-!
# Stage 1 (Euclidean): Differentiation operators on Mathlib test functions

This is a **Stage 1** building block for the plan in `tex/archive/HodgePlan-mc-28.1.26.rtf`.

Mathlib already provides:
- the LF-space `𝓓(Ω, F)` of compactly supported smooth functions on an open set `Ω ⊆ E`,
- the Fréchet spaces `𝓓_{K}(E, F)` of smooth functions supported in a fixed compact `K`,
- the continuous linear maps `ContDiffMapSupportedIn.iteratedFDerivLM` on `𝓓_{K}(E, F)`.

This file defines **derivative structure maps** from the LF-space `𝓓(Ω, F)` to bounded continuous
functions, using the universal property `TestFunction.mkCLM`.

These are the maps that control the LF topology, and they are the right prerequisite for defining
currents/distributions as continuous linear functionals.
-/

noncomputable section

open scoped Distributions BoundedContinuousFunction
open scoped BoundedContinuousFunction

namespace Hodge
namespace Analytic
namespace Stage1

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The target space for the `i`-th iterated derivative: continuous `i`-multilinear maps.  -/
abbrev IteratedFDerivTarget (i : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin i => E) F

/-- The `i`-th iterated derivative of a test function, bundled again as a test function.

This is *not* packaged as a continuous linear map yet (that requires proving continuity in the LF
topology), but it is the correct underlying object for building derivative-induced seminorms and,
ultimately, distributional differentials.
-/
noncomputable def iteratedFDerivTestFunction (i : ℕ) (f : 𝓓(Ω, F)) :
    𝓓(Ω, IteratedFDerivTarget (E := E) (F := F) i) := by
  classical
  refine
    { toFun := fun x => iteratedFDeriv ℝ i (f : E → F) x
      contDiff' := ?_
      hasCompactSupport' := ?_
      tsupport_subset' := ?_ }
  · -- smoothness (`C^∞`) of iterated derivatives
    -- Need `(↑⊤ : WithTop ℕ∞) + i ≤ ↑⊤` (note: `↑⊤` is *not* the top of `WithTop ℕ∞`).
    have hmn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (i : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      -- Avoid `simp` on the final goal (it can rewrite `x ≤ ⊤` to `True`).
      have hadd :
          (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (↑(i : ℕ∞) : WithTop ℕ∞) =
            (↑((⊤ : ℕ∞) + (i : ℕ∞)) : WithTop ℕ∞) := by
        simpa [WithTop.coe_add] using (WithTop.coe_add (⊤ : ℕ∞) (i : ℕ∞)).symm
      have hcoe :
          (↑((⊤ : ℕ∞) + (i : ℕ∞)) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
        exact (WithTop.coe_le_coe).2 (by simpa using (le_rfl : (⊤ : ℕ∞) ≤ ⊤))
      calc
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (i : WithTop ℕ∞)
            = (↑(⊤ : ℕ∞) : WithTop ℕ∞) + (↑(i : ℕ∞) : WithTop ℕ∞) := by simp
        _ ≤ (↑((⊤ : ℕ∞) + (i : ℕ∞)) : WithTop ℕ∞) := le_of_eq hadd
        _ ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := hcoe
    exact f.contDiff.iteratedFDeriv_right (m := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (i := i) (by
      simpa using hmn)
  · -- compact support is preserved under iterated derivatives
    simpa using (f.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) (n := i))
  · -- support control
    refine (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (n := i) (f := (f : E → F))).trans ?_
    exact f.tsupport_subset

/-- The `i`-th derivative as a bounded continuous function, obtained by bundling the derivative
as a test function then using Mathlib's canonical inclusion `𝓓(Ω, G) → E →ᵇ G`. -/
noncomputable def iteratedFDeriv_toBounded (i : ℕ) :
    𝓓(Ω, F) → (E →ᵇ IteratedFDerivTarget (E := E) (F := F) i) :=
  fun f =>
    (TestFunction.toBoundedContinuousFunctionCLM (Ω := Ω)
        (F := IteratedFDerivTarget (E := E) (F := F) i)
        (n := (⊤ : ℕ∞)) ℝ)
      (iteratedFDerivTestFunction (Ω := Ω) (F := F) i f)

/-- The `i`-th iterated derivative, as a **continuous** linear map from the LF-space `𝓓(Ω, F)` to
bounded continuous functions. -/
noncomputable def iteratedFDeriv_toBoundedCLM (i : ℕ) :
    𝓓(Ω, F) →L[ℝ] (E →ᵇ IteratedFDerivTarget (E := E) (F := F) i) :=
by
  classical
  -- Help typeclass inference for the codomain (required by `TestFunction.mkCLM`).
  letI : SeminormedAddCommGroup (E →ᵇ IteratedFDerivTarget (E := E) (F := F) i) := inferInstance
  letI : IsTopologicalAddGroup (E →ᵇ IteratedFDerivTarget (E := E) (F := F) i) :=
    SeminormedAddCommGroup.toIsTopologicalAddGroup
      (E := (E →ᵇ IteratedFDerivTarget (E := E) (F := F) i))
  letI : NormedSpace ℝ (E →ᵇ IteratedFDerivTarget (E := E) (F := F) i) := inferInstance
  letI : LocallyConvexSpace ℝ (E →ᵇ IteratedFDerivTarget (E := E) (F := F) i) :=
    NormedSpace.toLocallyConvexSpace
      (E := (E →ᵇ IteratedFDerivTarget (E := E) (F := F) i))
  letI : ContinuousSMul ℝ (E →ᵇ IteratedFDerivTarget (E := E) (F := F) i) := inferInstance
  refine
    TestFunction.mkCLM ℝ (iteratedFDeriv_toBounded (Ω := Ω) (F := F) i)
      (fun f g => ?_) (fun c f => ?_) (fun K K_sub_Ω => ?_)

  · -- additivity
    have hi : ((i : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
      (WithTop.coe_le_coe).2 (le_top : (i : ℕ∞) ≤ ⊤)
    ext x x'
    -- Reduce to the standard iterated-derivative addition lemma (pointwise in `x`, then evaluate
    -- the resulting multilinear maps at `x' : Fin i → E`).
    simpa [iteratedFDeriv_toBounded, iteratedFDerivTestFunction] using
      congrArg (fun h => (h x) x')
        (iteratedFDeriv_add (𝕜 := ℝ) (i := i)
          (f := (f : E → F)) (g := (g : E → F))
          (ContDiff.of_le f.contDiff hi) (ContDiff.of_le g.contDiff hi))

  · -- scalar multiplication
    have hi : ((i : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
      (WithTop.coe_le_coe).2 (le_top : (i : ℕ∞) ≤ ⊤)
    ext x x'
    -- Use the pointwise scalar-multiplication lemma for iterated derivatives.
    -- We use `ContDiffAt` obtained from `ContDiff` at order `↑i`.
    have hf : ContDiffAt ℝ (↑(i : ℕ) : WithTop ℕ∞) (f : E → F) x := by
      exact (ContDiff.of_le f.contDiff hi).contDiffAt
    simpa [iteratedFDeriv_toBounded, iteratedFDerivTestFunction] using
      congrArg (fun M => M x') (iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := i) (a := c)
        (f := (f : E → F)) (x := x) hf)

  · -- continuity on each compact-support piece
    -- On each fixed compact-support Fréchet space, this map is exactly `structureMapCLM`.
    have h :
        (iteratedFDeriv_toBounded (Ω := Ω) (F := F) i) ∘
            (TestFunction.ofSupportedIn (n := (⊤ : ℕ∞)) (Ω := Ω) (F := F) K_sub_Ω) =
          fun f : 𝓓_{K}(E, F) =>
            (ContDiffMapSupportedIn.structureMapCLM (𝕜 := ℝ) (E := E) (F := F)
                  (n := (⊤ : ℕ∞)) (K := K) i) f := by
      funext f
      ext x
      simp [iteratedFDeriv_toBounded, iteratedFDerivTestFunction]
    -- Transfer continuity across the pointwise equality `h`.
    have hcont :
        Continuous (fun f : 𝓓_{K}(E, F) =>
          (ContDiffMapSupportedIn.structureMapCLM (𝕜 := ℝ) (E := E) (F := F)
                (n := (⊤ : ℕ∞)) (K := K) i) f) :=
      (ContDiffMapSupportedIn.structureMapCLM (𝕜 := ℝ) (E := E) (F := F)
          (n := (⊤ : ℕ∞)) (K := K) i).continuous
    simpa [h] using hcont

end Stage1
end Analytic
end Hodge
