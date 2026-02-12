import Hodge.Analytic.Norms
import Hodge.Analytic.Forms

noncomputable section

open Classical Hodge

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! ## Codifferential (formal adjoint of d) -/

/-- Linear-map version of the Hodge star on k-forms. -/
noncomputable def hodgeStarLinear (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (2 * n - k) where
  toFun := hodgeStar (n := n) (X := X) (k := k)
  map_add' := by
    intro α β
    simpa using (hodgeStar_add (n := n) (X := X) (k := k) α β)
  map_smul' := by
    intro c α
    simpa using (hodgeStar_smul (n := n) (X := X) (k := k) c α)

/-- Codifferential `δ = (-1)^{(2n)k+2n+1} ⋆ d ⋆` as a linear map on k-forms.

The target degree is the literal output of `⋆ d ⋆`, i.e. `2n - (2n - k + 1)`,
which simplifies to `k - 1`. -/
noncomputable def codifferential (k : ℕ) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X (2 * n - (2 * n - k + 1)) := by
  classical
  let star_k : SmoothForm n X k →ₗ[ℂ] SmoothForm n X (2 * n - k) :=
    hodgeStarLinear (n := n) (X := X) (k := k)
  let d_nk : SmoothForm n X (2 * n - k) →ₗ[ℂ] SmoothForm n X (2 * n - k + 1) :=
    extDerivLinearMap n X (2 * n - k)
  let star_nk1 : SmoothForm n X (2 * n - k + 1) →ₗ[ℂ]
      SmoothForm n X (2 * n - (2 * n - k + 1)) :=
    hodgeStarLinear (n := n) (X := X) (k := 2 * n - k + 1)
  exact (codifferentialSign (2 * n) k : ℂ) • (star_nk1.comp (d_nk.comp star_k))

@[simp] theorem codifferential_zero (k : ℕ) :
    codifferential (n := n) (X := X) (k := k) 0 = 0 := by
  simpa using (codifferential (n := n) (X := X) (k := k)).map_zero

@[simp] theorem codifferential_add {k : ℕ} (α β : SmoothForm n X k) :
    codifferential (n := n) (X := X) (k := k) (α + β) =
      codifferential (n := n) (X := X) (k := k) α +
      codifferential (n := n) (X := X) (k := k) β := by
  simpa using (codifferential (n := n) (X := X) (k := k)).map_add α β

@[simp] theorem codifferential_smul {k : ℕ} (c : ℂ) (α : SmoothForm n X k) :
    codifferential (n := n) (X := X) (k := k) (c • α) =
      c • codifferential (n := n) (X := X) (k := k) α := by
  simpa using (codifferential (n := n) (X := X) (k := k)).map_smul c α

theorem codifferential_tsupport_subset {k : ℕ} (ω : SmoothForm n X k) :
    tsupport (codifferential (n := n) (X := X) (k := k) ω).as_alternating ⊆
      tsupport ω.as_alternating := by
  -- Step 1: tsupport control for ⋆ d ⋆.
  have hstar1 :
      tsupport (hodgeStar (n := n) (X := X) (k := k) ω).as_alternating ⊆
        tsupport ω.as_alternating :=
    hodgeStar_tsupport_subset (α := ω)
  have hderiv :
      tsupport
          (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
            (hodgeStar (n := n) (X := X) (k := k) ω)).as_alternating ⊆
        tsupport (hodgeStar (n := n) (X := X) (k := k) ω).as_alternating :=
    smoothExtDeriv_tsupport_subset (ω := hodgeStar (n := n) (X := X) (k := k) ω)
  have hstar2 :
      tsupport
          (hodgeStar (n := n) (X := X) (k := 2 * n - k + 1)
            (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
              (hodgeStar (n := n) (X := X) (k := k) ω))).as_alternating ⊆
        tsupport
          (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
            (hodgeStar (n := n) (X := X) (k := k) ω)).as_alternating :=
    hodgeStar_tsupport_subset
      (α := smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
        (hodgeStar (n := n) (X := X) (k := k) ω))
  have hcomp :
      tsupport
          (hodgeStar (n := n) (X := X) (k := 2 * n - k + 1)
            (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
              (hodgeStar (n := n) (X := X) (k := k) ω))).as_alternating ⊆
        tsupport ω.as_alternating :=
    hstar2.trans (hderiv.trans hstar1)
  -- Step 2: scalar factor doesn't enlarge support.
  have hsmul :
      tsupport
          ((codifferentialSign (2 * n) k : ℂ) •
              hodgeStar (n := n) (X := X) (k := 2 * n - k + 1)
                (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
                  (hodgeStar (n := n) (X := X) (k := k) ω))).as_alternating ⊆
        tsupport
          (hodgeStar (n := n) (X := X) (k := 2 * n - k + 1)
            (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
              (hodgeStar (n := n) (X := X) (k := k) ω))).as_alternating := by
    simpa [SmoothForm.smul_apply] using
      (tsupport_smul_subset_right
        (f := fun _ : X => (codifferentialSign (2 * n) k : ℂ))
        (g :=
          (hodgeStar (n := n) (X := X) (k := 2 * n - k + 1)
            (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
              (hodgeStar (n := n) (X := X) (k := k) ω))).as_alternating))
  -- Step 3: unfold codifferential and combine.
  have hcod :
      tsupport (codifferential (n := n) (X := X) (k := k) ω).as_alternating ⊆
        tsupport
          (hodgeStar (n := n) (X := X) (k := 2 * n - k + 1)
            (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
              (hodgeStar (n := n) (X := X) (k := k) ω))).as_alternating := by
    simpa [codifferential, hodgeStarLinear, smoothExtDeriv, extDerivLinearMap, SmoothForm.smul_apply]
      using hsmul
  exact hcod.trans hcomp

theorem codifferential_hasCompactSupport {k : ℕ} (ω : SmoothForm n X k) :
    HasCompactSupport ω.as_alternating →
      HasCompactSupport (codifferential (n := n) (X := X) (k := k) ω).as_alternating := by
  intro hcomp
  have hstar1 :
      HasCompactSupport (hodgeStar (n := n) (X := X) (k := k) ω).as_alternating :=
    hodgeStar_hasCompactSupport (α := ω) hcomp
  have hderiv :
      HasCompactSupport
        (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
          (hodgeStar (n := n) (X := X) (k := k) ω)).as_alternating :=
    smoothExtDeriv_hasCompactSupport
      (ω := hodgeStar (n := n) (X := X) (k := k) ω) hstar1
  have hstar2 :
      HasCompactSupport
        (hodgeStar (n := n) (X := X) (k := 2 * n - k + 1)
          (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
            (hodgeStar (n := n) (X := X) (k := k) ω))).as_alternating :=
    hodgeStar_hasCompactSupport
      (α := smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
        (hodgeStar (n := n) (X := X) (k := k) ω)) hderiv
  have hsmul :
      HasCompactSupport
        ((fun _ : X => (codifferentialSign (2 * n) k : ℂ)) •
          (hodgeStar (n := n) (X := X) (k := 2 * n - k + 1)
            (smoothExtDeriv (n := n) (X := X) (k := 2 * n - k)
              (hodgeStar (n := n) (X := X) (k := k) ω))).as_alternating) :=
    HasCompactSupport.smul_left (f := fun _ : X => (codifferentialSign (2 * n) k : ℂ)) hstar2
  simpa [codifferential, hodgeStarLinear, smoothExtDeriv, extDerivLinearMap, SmoothForm.smul_apply]
    using hsmul

end
