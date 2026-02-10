import Hodge.Analytic.Advanced.ContMDiffForms
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Classical Manifold Filter
open scoped Manifold

namespace ContMDiffForm

set_option autoImplicit false

universe u v

variable {n : ℕ} {k : ℕ}
variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X] [IsManifold (𝓒_complex n) ⊤ X]
variable {Y : Type v} [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) Y] [IsManifold (𝓒_complex n) ⊤ Y]

/-- Chart-level representation of a map `f` in coordinates at `x₀`. -/
noncomputable def fChart (f : X → Y) (x₀ : X) : TangentModel n → TangentModel n :=
  fun u =>
    (chartAt (EuclideanSpace ℂ (Fin n)) (f x₀))
      (f ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u))

omit [IsManifold (𝓒_complex n) ⊤ X] [IsManifold (𝓒_complex n) ⊤ Y] in
lemma mfderiv_eq_fderiv_fChart (f : X → Y) (x₀ y : X)
    [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n Y]
    (hx : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy : f y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (f x₀)).source)
    (hf : MDifferentiableAt (𝓒_complex n) (𝓒_complex n) f y) :
    mfderiv (𝓒_complex n) (𝓒_complex n) f y =
      fderiv ℝ (fChart (n := n) f x₀)
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) y) := by
  classical
  -- Charts are locally constant on chart sources.
  have hchart :
      chartAt (EuclideanSpace ℂ (Fin n)) y =
        chartAt (EuclideanSpace ℂ (Fin n)) x₀ :=
    (HasLocallyConstantCharts.hCharts (n := n) (X := X) (x := x₀) (y := y) hx)
  have hchart_f :
      chartAt (EuclideanSpace ℂ (Fin n)) (f y) =
        chartAt (EuclideanSpace ℂ (Fin n)) (f x₀) :=
    (HasLocallyConstantCharts.hCharts (n := n) (X := Y) (x := f x₀) (y := f y) hy)
  -- Simplify the written-in-chart expression to `fChart`.
  have h_written :
      writtenInExtChartAt (𝓒_complex n) (𝓒_complex n) y f =
        fChart (n := n) f x₀ := by
    funext u
    simp [writtenInExtChartAt, fChart, 𝓒_complex, hchart, hchart_f]
  -- Range of the model with corners is all of `TangentModel n`.
  have h_range : Set.range (𝓒_complex n) = (Set.univ : Set (TangentModel n)) := by
    simp [𝓒_complex, modelWithCornersSelf_coe, Set.range_id]
  -- Now unfold `mfderiv` and rewrite.
  have hf' : MDifferentiableAt 𝓘(ℝ, TangentModel n) 𝓘(ℝ, TangentModel n) f y := by
    simpa [𝓒_complex] using hf
  have h_fun :
      (chartAt (EuclideanSpace ℂ (Fin n)) (f y)) ∘ f ∘
          (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm =
        fChart (n := n) f x₀ := by
    funext u
    simp [fChart, hchart_f]
  -- Unfold `mfderiv` to `fderivWithin`, then rewrite the function.
  have h_simp :
      fderiv ℝ
          (chartAt (EuclideanSpace ℂ (Fin n)) (f y) ∘ f ∘
            (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm)
          ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) y) =
        fderiv ℝ (fChart (n := n) f x₀)
          ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) y) := by
    simp [h_fun]
  -- Now unfold `mfderiv` and reduce to `h_simp`.
  simpa [mfderiv, hf', h_range, fderivWithin_univ, extChartAt_coe, 𝓒_complex,
    modelWithCornersSelf_coe, hchart] using h_simp

/-- Pullback of a `ContMDiffForm` (WIP). -/
noncomputable def pullbackFun (f : X → Y) (ω : ContMDiffForm n Y k) : X → FiberAlt n k :=
  fun x =>
    (ω.as_alternating (f x)).compContinuousLinearMap
      (mfderiv (𝓒_complex n) (𝓒_complex n) f x)

/-- Pullback of a `ContMDiffForm` along a smooth map (WIP). -/
noncomputable def pullback (f : X → Y) (ω : ContMDiffForm n Y k) :
    ContMDiffForm n X k :=
  { as_alternating := pullbackFun (n := n) (f := f) ω
    smooth' := by
      -- TODO: show smoothness using `ContMDiff` of `f` and `ω`.
      sorry }

@[simp] lemma pullback_as_alternating (f : X → Y) (ω : ContMDiffForm n Y k) (x : X) :
    (pullback (n := n) (f := f) ω).as_alternating x =
      (ω.as_alternating (f x)).compContinuousLinearMap
        (mfderiv (𝓒_complex n) (𝓒_complex n) f x) := rfl

/-- Pullback commutes with `extDerivForm` (WIP). -/
theorem extDerivForm_pullback {k : ℕ} (f : X → Y) (ω : ContMDiffForm n Y k)
    [HasLocallyConstantCharts n X] [HasLocallyConstantCharts n Y]
    (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f) :
    extDerivForm (pullback (n := n) (f := f) ω) HasLocallyConstantCharts.hCharts =
      pullback (n := n) (f := f) (extDerivForm ω HasLocallyConstantCharts.hCharts) := by
  -- Reduce to a pointwise statement on `extDerivAt`.
  ext x
  -- Unfold `extDerivForm` to `extDerivAt` (avoid expanding `extDerivAt`).
  simp [extDerivForm_as_alternating, extDeriv_as_alternating, pullback_as_alternating,
    -extDerivAt_def]
  -- Work in the preferred chart at `x`.
  -- This is a chart-level pullback identity; see `extDeriv_pullback` in Mathlib.
  set x₀ : X := x
  set y₀ : Y := f x₀
  set u₀ : TangentModel n := (chartAt (EuclideanSpace ℂ (Fin n)) x₀) x₀
  -- Chart-level representation of `f` at `x₀`.
  let f_chart : TangentModel n → TangentModel n :=
    fun u =>
      (chartAt (EuclideanSpace ℂ (Fin n)) y₀) (f ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u))
  -- `f` is continuous at `x₀`, hence maps a neighborhood into the chart source at `y₀`.
  have hcont : ContinuousAt f x₀ :=
    (ContMDiffAt.continuousAt (hf x₀))
  have h_f_source :
      f ⁻¹' (chartAt (EuclideanSpace ℂ (Fin n)) y₀).source ∈ nhds x₀ := by
    refine hcont.preimage_mem_nhds ?_
    exact (chartAt (EuclideanSpace ℂ (Fin n)) y₀).open_source.mem_nhds (mem_chart_source _ y₀)
  have h_target :
      (chartAt (EuclideanSpace ℂ (Fin n)) x₀).target ∈ nhds u₀ := by
    refine (chartAt (EuclideanSpace ℂ (Fin n)) x₀).open_target.mem_nhds ?_
    exact (chartAt (EuclideanSpace ℂ (Fin n)) x₀).map_source (mem_chart_source _ x₀)
  have h_pre :
      (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm ⁻¹'
        (f ⁻¹' (chartAt (EuclideanSpace ℂ (Fin n)) y₀).source) ∈ nhds u₀ := by
    -- continuity of the inverse chart at `u₀`
    have hcont_symm :
        ContinuousAt (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u₀ := by
      refine (chartAt (EuclideanSpace ℂ (Fin n)) x₀).continuousAt_symm ?_
      exact (chartAt (EuclideanSpace ℂ (Fin n)) x₀).map_source (mem_chart_source _ x₀)
    have hx₀ : x₀ ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := mem_chart_source _ x₀
    have hu₀ : (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u₀ = x₀ := by
      simp [u₀, (chartAt (EuclideanSpace ℂ (Fin n)) x₀).left_inv hx₀]
    have h_f_source' :
        f ⁻¹' (chartAt (EuclideanSpace ℂ (Fin n)) y₀).source ∈
          nhds ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u₀) := by
      simpa [hu₀] using h_f_source
    exact hcont_symm.preimage_mem_nhds h_f_source'
  -- Eventual equality of the chart-level pullback formula.
  have h_eventually :
      omegaInChart (pullback (n := n) (f := f) ω) x₀ =ᶠ[nhds u₀]
        (fun u =>
          (omegaInChart ω y₀ (f_chart u)).compContinuousLinearMap (fderiv ℝ f_chart u)) := by
    filter_upwards [Filter.inter_mem h_target h_pre] with u hu
    have hu_target : u ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).target := hu.1
    have hu_pre :
        u ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm ⁻¹'
          (f ⁻¹' (chartAt (EuclideanSpace ℂ (Fin n)) y₀).source) := hu.2
    set y := (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u
    have hx : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
      exact (chartAt (EuclideanSpace ℂ (Fin n)) x₀).map_target hu_target
    have hy : f y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) y₀).source := by
      simpa [y] using hu_pre
    have hmdiff : MDifferentiableAt (𝓒_complex n) (𝓒_complex n) f y :=
      (hf y).mdifferentiableAt (by simp)
    -- rewrite the pullback formula using the chart-level derivative.
    have hmf :
        mfderiv (𝓒_complex n) (𝓒_complex n) f y =
          fderiv ℝ (fChart (n := n) f x₀)
            ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) y) :=
      mfderiv_eq_fderiv_fChart (n := n) (f := f) (x₀ := x₀) (y := y) hx hy hmdiff
    -- Now simplify both sides.
    have hchart_x : (chartAt (EuclideanSpace ℂ (Fin n)) x₀) y = u := by
      simpa [y] using (chartAt (EuclideanSpace ℂ (Fin n)) x₀).right_inv hu_target
    -- reduce both sides to the same chart-level expression
    have h_chart : f_chart = fChart (n := n) f x₀ := by
      rfl
    have hy' : f ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u) ∈
        (chartAt (EuclideanSpace ℂ (Fin n)) y₀).source := by
      simpa [y] using hy
    have hchart_eval :
        (chartAt (EuclideanSpace ℂ (Fin n)) y₀).symm
            ((chartAt (EuclideanSpace ℂ (Fin n)) (f x₀))
              (f ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u))) =
          f ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u) := by
      simpa [y₀] using (chartAt (EuclideanSpace ℂ (Fin n)) y₀).left_inv hy'
    simp [omegaInChart, pullback, pullbackFun, y, h_chart, hmf, hchart_x, fChart, hchart_eval]
  have h_ext_eq :
      _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
        (omegaInChart (pullback (n := n) (f := f) ω) x₀) u₀ =
        _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
          (fun u =>
            (omegaInChart ω y₀ (f_chart u)).compContinuousLinearMap (fderiv ℝ f_chart u)) u₀ :=
    Filter.EventuallyEq.extDeriv_eq h_eventually
  -- `omegaInChart` is smooth, hence differentiable at the needed point.
  have hy0 : f_chart u₀ ∈ (chartAt (EuclideanSpace ℂ (Fin n)) y₀).target := by
    simp [f_chart, u₀, y₀, (chartAt (EuclideanSpace ℂ (Fin n)) y₀).map_source (mem_chart_source _ y₀)]
  have htarget_y : (chartAt (EuclideanSpace ℂ (Fin n)) y₀).target ∈ nhds (f_chart u₀) := by
    exact (chartAt (EuclideanSpace ℂ (Fin n)) y₀).open_target.mem_nhds hy0
  have hω_contDiff :
      ContDiffAt ℝ ⊤ (omegaInChart ω y₀) (f_chart u₀) :=
    (contDiffOn_omegaInChart ω y₀).contDiffAt htarget_y
  have hω : DifferentiableAt ℝ (omegaInChart ω y₀) (f_chart u₀) :=
    hω_contDiff.differentiableAt (by simp)
  -- Smoothness of the chart-level map.
  have h_chart_symm :
      ContMDiffAt (𝓒_complex n) (𝓒_complex n) ⊤
        (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u₀ := by
    have hOn :=
      contMDiffOn_chart_symm (I := 𝓒_complex n) (H := EuclideanSpace ℂ (Fin n)) (x := x₀)
        (n := (⊤ : WithTop ℕ∞))
    exact hOn.contMDiffAt h_target
  have h_f : ContMDiffAt (𝓒_complex n) (𝓒_complex n) ⊤ f x₀ := hf x₀
  have h_chart_y :
      ContMDiffAt (𝓒_complex n) (𝓒_complex n) ⊤
        (chartAt (EuclideanSpace ℂ (Fin n)) y₀) y₀ := by
    have hOn :=
      contMDiffOn_chart (I := 𝓒_complex n) (H := EuclideanSpace ℂ (Fin n)) (x := y₀)
        (n := (⊤ : WithTop ℕ∞))
    have htarget_y' :
        (chartAt (EuclideanSpace ℂ (Fin n)) y₀).source ∈ nhds y₀ := by
      exact (chartAt (EuclideanSpace ℂ (Fin n)) y₀).open_source.mem_nhds (mem_chart_source _ y₀)
    exact hOn.contMDiffAt htarget_y'
  have h_comp1 :
      ContMDiffAt (𝓒_complex n) (𝓒_complex n) ⊤
        (f ∘ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm) u₀ := by
    have hx₀ : x₀ ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := mem_chart_source _ x₀
    have hu₀ : (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u₀ = x₀ := by
      simp [u₀, (chartAt (EuclideanSpace ℂ (Fin n)) x₀).left_inv hx₀]
    have h_f' : ContMDiffAt (𝓒_complex n) (𝓒_complex n) ⊤ f
        ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u₀) := by
      simpa [hu₀] using h_f
    exact h_f'.comp u₀ h_chart_symm
  have h_comp2 :
      ContMDiffAt (𝓒_complex n) (𝓒_complex n) ⊤
        (fun u =>
          (chartAt (EuclideanSpace ℂ (Fin n)) y₀)
            (f ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u))) u₀ := by
    have hx₀ : x₀ ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := mem_chart_source _ x₀
    have hu₀ : (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u₀ = x₀ := by
      simp [u₀, (chartAt (EuclideanSpace ℂ (Fin n)) x₀).left_inv hx₀]
    have h_chart_y' :
        ContMDiffAt (𝓒_complex n) (𝓒_complex n) ⊤
          (chartAt (EuclideanSpace ℂ (Fin n)) y₀) (f ((chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm u₀)) := by
      simpa [hu₀] using h_chart_y
    exact h_chart_y'.comp u₀ h_comp1
  have hf_chart : ContDiffAt ℝ ⊤ f_chart u₀ := by
    simpa [f_chart, 𝓒_complex] using
      (ContMDiffAt.contDiffAt (n := (⊤ : WithTop ℕ∞)) h_comp2)
  -- Apply the Euclidean pullback lemma.
  have h_ext_pullback :
      _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
        (fun u =>
          (omegaInChart ω y₀ (f_chart u)).compContinuousLinearMap
            (fderiv ℝ f_chart u)) u₀ =
        (_root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k) (omegaInChart ω y₀)
            (f_chart u₀)).compContinuousLinearMap (fderiv ℝ f_chart u₀) := by
    have hr : minSmoothness ℝ 2 ≤ (⊤ : WithTop ℕ∞) := by simp
    simpa using (extDeriv_pullback (ω := omegaInChart ω y₀) (f := f_chart) (x := u₀)
      (hω := hω) (hf := hf_chart) (r := ⊤) hr)
  -- Compare the manifold `extDerivAt` to chart-level `extDeriv`.
  have h_chart_pull :
      extDerivAt (pullback (n := n) (f := f) ω) x₀ =
        _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
          (omegaInChart (pullback (n := n) (f := f) ω) x₀) u₀ := by
    simpa [x₀, u₀] using
      (extDerivAt_eq_chart_extDeriv (ω := pullback (n := n) (f := f) ω) x₀)
  have h_chart_ω :
      extDerivAt ω y₀ =
        _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
          (omegaInChart ω y₀) (f_chart u₀) := by
    -- `f_chart u₀ = (chartAt y₀) y₀`
    have : f_chart u₀ = (chartAt (EuclideanSpace ℂ (Fin n)) y₀) y₀ := by
      simp [f_chart, u₀, y₀]
    simpa [this, y₀] using (extDerivAt_eq_chart_extDeriv (ω := ω) y₀)
  -- Put everything together.
  have hfinal :
      extDerivAt (pullback (n := n) (f := f) ω) x₀ =
        (extDerivAt ω y₀).compContinuousLinearMap
          (mfderiv (𝓒_complex n) (𝓒_complex n) f x₀) := by
    calc
      extDerivAt (pullback (n := n) (f := f) ω) x₀
          = _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
              (omegaInChart (pullback (n := n) (f := f) ω) x₀) u₀ := h_chart_pull
      _ = _root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k)
            (fun u =>
              (omegaInChart ω y₀ (f_chart u)).compContinuousLinearMap (fderiv ℝ f_chart u)) u₀ := h_ext_eq
      _ = (_root_.extDeriv (E := TangentModel n) (F := ℂ) (n := k) (omegaInChart ω y₀)
            (f_chart u₀)).compContinuousLinearMap (fderiv ℝ f_chart u₀) := h_ext_pullback
      _ = (extDerivAt ω y₀).compContinuousLinearMap
            (mfderiv (𝓒_complex n) (𝓒_complex n) f x₀) := by
            -- Use the chart-level identification of `mfderiv` at `x₀`.
            have hx₀ : x₀ ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := mem_chart_source _ x₀
            have hy₀ : f x₀ ∈ (chartAt (EuclideanSpace ℂ (Fin n)) y₀).source := mem_chart_source _ y₀
            have hmf₀ :
                mfderiv (𝓒_complex n) (𝓒_complex n) f x₀ =
                  fderiv ℝ (fChart (n := n) f x₀)
                    ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) x₀) :=
              mfderiv_eq_fderiv_fChart (n := n) (f := f) (x₀ := x₀) (y := x₀) hx₀ hy₀
                ((hf x₀).mdifferentiableAt (by simp))
            -- Rewrite with `h_chart_ω` and `hmf₀`.
            have h_chart : f_chart = fChart (n := n) f x₀ := by
              rfl
            have hfun : fderiv ℝ f_chart u₀ = fderiv ℝ (fChart (n := n) f x₀)
                ((chartAt (EuclideanSpace ℂ (Fin n)) x₀) x₀) := by
              simp [h_chart, u₀]
            -- Now finish.
            rw [← h_chart_ω]
            simp [hfun, hmf₀]
  -- Apply the equality to the test vector.
  rename_i v
  simpa using congrArg (fun L => L v) hfinal

end ContMDiffForm
