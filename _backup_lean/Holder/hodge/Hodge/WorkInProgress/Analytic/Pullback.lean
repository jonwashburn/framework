import Hodge.Analytic.FormType
import Hodge.Analytic.Forms
import Hodge.WorkInProgress.Analytic.ContMDiffPullback

noncomputable section

open Classical Manifold
open scoped Manifold

set_option autoImplicit false

universe u v

variable {n : ℕ} {k : ℕ}

/-- Pull back a fiberwise alternating form along a linear map on the model tangent space. -/
def fiberPullback (L : TangentModel n →L[ℝ] TangentModel n) (ω : FiberAlt n k) : FiberAlt n k :=
  ω.compContinuousLinearMap L

lemma fiberPullback_norm_le (L : TangentModel n →L[ℝ] TangentModel n) (ω : FiberAlt n k) :
    ‖fiberPullback (n := n) L ω‖ ≤ ‖ω‖ * ‖L‖ ^ k := by
  simpa [fiberPullback] using
    (ContinuousAlternatingMap.norm_compContinuousLinearMap_le (f := ω) (g := L))

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
variable {Y : Type v} [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) Y] [IsManifold (𝓒_complex n) ⊤ Y]

/-- Pullback of smooth forms along a smooth map (WIP). -/
noncomputable def smoothFormPullbackFun {k : ℕ} (f : X → Y) (ω : SmoothForm n Y k) :
    X → FiberAlt n k :=
  fun x =>
    fiberPullback (n := n)
      (mfderiv (𝓒_complex n) (𝓒_complex n) f x) (ω.as_alternating (f x))

/-- Pullback of smooth forms along a smooth map (WIP). -/
noncomputable def smoothFormPullback {k : ℕ} (f : X → Y) (ω : SmoothForm n Y k) :
    SmoothForm n X k :=
  { as_alternating := smoothFormPullbackFun (n := n) (f := f) ω
    is_smooth := by
      -- TODO: prove smoothness using `ContMDiff` of `f` and `ω`.
      sorry }

namespace SmoothForm

variable {k : ℕ}

lemma pullback_toContMDiffForm (f : X → Y) (ω : SmoothForm n Y k) :
    (smoothFormPullback (n := n) f ω).toContMDiffForm =
      ContMDiffForm.pullback (n := n) (f := f) ω.toContMDiffForm := by
  refine ContMDiffForm.ext _ _ (fun x => ?_)
  simp [smoothFormPullback, smoothFormPullbackFun, fiberPullback, ContMDiffForm.pullback,
    ContMDiffForm.pullbackFun]

end SmoothForm

/-- Pullback commutes with the exterior derivative (WIP). -/
theorem smoothExtDeriv_pullback {k : ℕ} (f : X → Y) (ω : SmoothForm n Y k)
    [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n Y]
    (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f) :
    smoothFormPullback (n := n) f (smoothExtDeriv ω) =
      smoothExtDeriv (smoothFormPullback (n := n) f ω) := by
  -- Use the `ContMDiffForm` naturality of `extDerivForm`, then convert back.
  -- Rewrite `smoothExtDeriv` through `extDerivForm`.
  ext x v
  have h :=
    ContMDiffForm.extDerivForm_pullback (n := n) (k := k) (f := f)
      (ω := ω.toContMDiffForm) hf
  have h' :
      ContMDiffForm.extDerivForm (smoothFormPullback (n := n) f ω).toContMDiffForm
          HasLocallyConstantCharts.hCharts =
        ContMDiffForm.pullback (n := n) (f := f)
          (ContMDiffForm.extDerivForm ω.toContMDiffForm HasLocallyConstantCharts.hCharts) := by
    simpa [SmoothForm.pullback_toContMDiffForm] using h
  have h'' := congrArg (fun η => (η.toSmoothForm.as_alternating x) v) h'
  -- Unfold the `SmoothForm` pullback/evaluation to match the chart-level statement.
  simpa [smoothExtDeriv_eq_extDerivForm, smoothFormPullbackFun, fiberPullback,
    ContMDiffForm.pullback, ContMDiffForm.pullbackFun, ContMDiffForm.extDerivForm_as_alternating,
    ContMDiffForm.extDerivAt_def, SmoothForm.toContMDiffForm_as_alternating] using h''.symm

namespace SmoothForm

variable {k : ℕ}

@[simp] theorem pullback_as_alternating (f : X → Y) (ω : SmoothForm n Y k) (x : X) :
    (smoothFormPullback (n := n) f ω).as_alternating x =
      fiberPullback (n := n)
        (mfderiv (𝓒_complex n) (𝓒_complex n) f x) (ω.as_alternating (f x)) := rfl

variable [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n Y]

@[simp] theorem pullback_add (f : X → Y) (ω₁ ω₂ : SmoothForm n Y k) :
    smoothFormPullback (n := n) f (ω₁ + ω₂) =
      smoothFormPullback (n := n) f ω₁ + smoothFormPullback (n := n) f ω₂ := by
  ext x v
  simp [fiberPullback, SmoothForm.add_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.add_apply]

@[simp] theorem pullback_smul (f : X → Y) (c : ℝ) (ω : SmoothForm n Y k) :
    smoothFormPullback (n := n) f (c • ω) =
      c • smoothFormPullback (n := n) f ω := by
  ext x v
  simp [fiberPullback, SmoothForm.smul_real_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply]

@[simp] theorem pullback_zero (f : X → Y) :
    smoothFormPullback (n := n) f (0 : SmoothForm n Y k) = 0 := by
  ext x v
  simp [fiberPullback,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]

end SmoothForm
