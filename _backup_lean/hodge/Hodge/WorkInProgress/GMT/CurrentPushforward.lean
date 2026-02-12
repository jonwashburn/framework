import Hodge.Analytic.Currents
import Hodge.WorkInProgress.Analytic.Pullback

noncomputable section

open Classical

namespace Hodge.GMT

universe u v

variable {n : ℕ} {k : ℕ}
variable {X : Type u} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type v} [MetricSpace Y] [ChartedSpace (EuclideanSpace ℂ (Fin n)) Y]
  [IsManifold (𝓒_complex n) ⊤ Y] [ProjectiveComplexManifold n Y] [KahlerManifold n Y]
  [Nonempty Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Comass bound for pullback along a map, given a uniform derivative bound. -/
theorem comass_pullback_le (f : X → Y) (C : ℝ)
    (hC : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C)
    (ω : SmoothForm n Y k) :
    comass (smoothFormPullback (n := n) (f := f) ω) ≤ comass ω * C := by
  classical
  have h_pointwise :
      ∀ x,
        pointwiseComass (n := n) (X := X) (k := k)
          (smoothFormPullback (n := n) (f := f) ω) x ≤ comass ω * C := by
    intro x
    have h_pull :
        ‖fiberPullback (n := n)
            (mfderiv (𝓒_complex n) (𝓒_complex n) f x) (ω.as_alternating (f x))‖ ≤
          ‖ω.as_alternating (f x)‖ *
            ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k := by
      simpa using
        (fiberPullback_norm_le (n := n)
          (L := mfderiv (𝓒_complex n) (𝓒_complex n) f x)
          (ω := ω.as_alternating (f x)))
    have hω :
        ‖ω.as_alternating (f x)‖ ≤ comass ω := by
      have hmem : pointwiseComass (n := n) (X := Y) (k := k) ω (f x) ∈
          Set.range (pointwiseComass (n := n) (X := Y) (k := k) ω) :=
        ⟨f x, rfl⟩
      have hsup :=
        le_csSup (comass_bddAbove (n := n) (X := Y) (k := k) ω) hmem
      simpa [pointwiseComass] using hsup
    have hmf : ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C := hC x
    have h_mul :
        ‖ω.as_alternating (f x)‖ *
            ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤
          comass ω * C := by
      have hω_nonneg : 0 ≤ ‖ω.as_alternating (f x)‖ := norm_nonneg _
      have hmf_nonneg : 0 ≤ ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k := by
        exact pow_nonneg (norm_nonneg _) _
      exact mul_le_mul hω hmf hmf_nonneg (comass_nonneg (n := n) (X := Y) (k := k) ω)
    have h_pointwise' :
        pointwiseComass (n := n) (X := X) (k := k)
          (smoothFormPullback (n := n) (f := f) ω) x ≤
          ‖ω.as_alternating (f x)‖ *
            ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k := by
      simpa [pointwiseComass] using h_pull
    exact h_pointwise'.trans h_mul
  -- take supremum over x
  unfold comass
  apply csSup_le
  · rcases Classical.choice (inferInstance : Nonempty X) with x₀
    exact ⟨pointwiseComass (n := n) (X := X) (k := k)
      (smoothFormPullback (n := n) (f := f) ω) x₀, ⟨x₀, rfl⟩⟩
  · intro r hr
    rcases hr with ⟨x, rfl⟩
    exact h_pointwise x

/-- Linear pullback on smooth forms (WIP). -/
noncomputable def smoothFormPullbackLinear (f : X → Y) (C : ℝ)
    (hC : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C) :
    SmoothForm n Y k →L[ℝ] SmoothForm n X k := by
  classical
  -- Build the underlying linear map from pointwise pullback.
  let L : SmoothForm n Y k →ₗ[ℝ] SmoothForm n X k :=
    { toFun := smoothFormPullback (n := n) (f := f)
      map_add' := by
        intro ω₁ ω₂
        simpa using (SmoothForm.pullback_add (n := n) (f := f) ω₁ ω₂)
      map_smul' := by
        intro r ω
        simpa using (SmoothForm.pullback_smul (n := n) (f := f) r ω) }
  -- Use the uniform comass bound from `comass_pullback_le`.
  exact L.mkContinuous C (by
    intro ω
    have hcomass := comass_pullback_le (n := n) (k := k) (f := f) (C := C) hC ω
    simpa [mul_comm] using hcomass)

/-- Pushforward of currents along a smooth map (WIP). -/
noncomputable def currentPushforward (f : X → Y) (C : ℝ)
    (hC : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C)
    (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (T : Current n X k) : Current n Y k :=
  { toFun := T.toFun.comp (smoothFormPullbackLinear (n := n) (k := k) f C hC)
    boundary_bound := by
      cases k with
      | zero =>
          -- No boundary in degree 0.
          exact True.intro
      | succ k' =>
          -- Use the boundary bound of `T` in degree `k'`.
          obtain ⟨M, hM⟩ :=
            (T.boundary_bound :
              ∃ M : ℝ, ∀ ω : SmoothForm n X k', |T.toFun (smoothExtDeriv ω)| ≤ M * ‖ω‖)
          -- Derivative bound for degree `k'` forms (use `max 1 C`).
          set C' : ℝ := max 1 C
          have hC' : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤ C' := by
            intro x
            by_cases hle : ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ≤ 1
            · have hpow :
                ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤ 1 := by
                have hpow' :
                    ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤
                      ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ 0 :=
                  pow_le_pow_of_le_one (norm_nonneg _) hle (Nat.zero_le _)
                simpa using hpow'
              exact hpow.trans (le_max_left _ _)
            · have hlt : 1 < ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ :=
                lt_of_not_ge hle
              have hle1 : (1 : ℝ) ≤ ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ :=
                le_of_lt hlt
              have hpow :
                  ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤
                    ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ (k' + 1) := by
                have hnonneg : 0 ≤ ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' :=
                  pow_nonneg (norm_nonneg _) _
                have hmul :
                    ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤
                      ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' *
                        ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ :=
                  le_mul_of_one_le_right hnonneg hle1
                simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul
              have hpow' :
                  ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤ C :=
                hpow.trans (hC x)
              exact hpow'.trans (le_max_right _ _)
          refine ⟨|M| * C', ?_⟩
          intro ω
          have hcomm :
              smoothFormPullback (n := n) f (smoothExtDeriv ω) =
                smoothExtDeriv (smoothFormPullback (n := n) f ω) := by
            simpa using (smoothExtDeriv_pullback (n := n) (f := f) (ω := ω) hf)
          have hT :
              |T.toFun (smoothExtDeriv (smoothFormPullback (n := n) (f := f) ω))| ≤
                M * ‖smoothFormPullback (n := n) (f := f) ω‖ :=
            hM (smoothFormPullback (n := n) (f := f) ω)
          have hMle :
              M * ‖smoothFormPullback (n := n) (f := f) ω‖ ≤
                |M| * ‖smoothFormPullback (n := n) (f := f) ω‖ := by
            have hnorm_nonneg : 0 ≤ ‖smoothFormPullback (n := n) (f := f) ω‖ := norm_nonneg _
            exact mul_le_mul_of_nonneg_right (le_abs_self M) hnorm_nonneg
          have hnorm :
              ‖smoothFormPullback (n := n) (f := f) ω‖ ≤ ‖ω‖ * C' := by
            -- `‖·‖` is the comass norm.
            change comass (smoothFormPullback (n := n) (f := f) ω) ≤ comass ω * C'
            simpa [C'] using (comass_pullback_le (n := n) (k := k') (f := f) (C := C') hC' ω)
          have habs :
              |M| * ‖smoothFormPullback (n := n) (f := f) ω‖ ≤ |M| * (‖ω‖ * C') :=
            mul_le_mul_of_nonneg_left hnorm (abs_nonneg M)
          calc
            |(T.toFun.comp (smoothFormPullbackLinear (n := n) (k := k' + 1) f C hC)) (smoothExtDeriv ω)| =
                |T.toFun (smoothExtDeriv (smoothFormPullback (n := n) (f := f) ω))| := by
                  simp [smoothFormPullbackLinear, hcomm]
            _ ≤ |M| * ‖smoothFormPullback (n := n) (f := f) ω‖ := hT.trans hMle
            _ ≤ |M| * (‖ω‖ * C') := habs
            _ = |M| * C' * ‖ω‖ := by
                  simp [mul_comm, mul_left_comm, mul_assoc] }

end Hodge.GMT
