import Hodge.Analytic.Laplacian.Codifferential

/-!
# Hodge Laplacian Δ

This module introduces a structurally correct definition of the **Hodge Laplacian**
\(\Delta = d\delta + \delta d\) on smooth forms.

The deeper analytic results (ellipticity, finite-dimensionality of harmonic forms,
Hodge decomposition) are developed in subsequent files.
-/

noncomputable section

open Classical

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! Local cast helpers (distribute `castForm` over algebraic operations). -/

private lemma castForm_add {k k' : ℕ} (h : k = k') (ω η : SmoothForm n X k) :
    castForm (n := n) (X := X) h (ω + η) =
      castForm (n := n) (X := X) h ω + castForm (n := n) (X := X) h η := by
  subst h; rfl

private lemma castForm_smul {k k' : ℕ} (h : k = k') (c : ℂ) (ω : SmoothForm n X k) :
    castForm (n := n) (X := X) h (c • ω) =
      c • castForm (n := n) (X := X) h ω := by
  subst h; rfl

private lemma eventuallyEq_zero_add {k : ℕ} (ω η : SmoothForm n X k) {x : X}
    (hω : ω.as_alternating =ᶠ[nhds x] 0) (hη : η.as_alternating =ᶠ[nhds x] 0) :
    (fun y => ω.as_alternating y + η.as_alternating y) =ᶠ[nhds x] 0 := by
  rcases (Filter.eventuallyEq_iff_exists_mem).1 hω with ⟨s, hs, hsEq⟩
  rcases (Filter.eventuallyEq_iff_exists_mem).1 hη with ⟨t, ht, htEq⟩
  refine Filter.eventuallyEq_of_mem (Filter.inter_mem hs ht) ?_
  intro y hy
  have hyS : y ∈ s := hy.1
  have hyT : y ∈ t := hy.2
  simp [hsEq hyS, htEq hyT]

private lemma tsupport_add_subset {k : ℕ} (ω η : SmoothForm n X k) :
    tsupport (ω + η).as_alternating ⊆
      tsupport ω.as_alternating ∪ tsupport η.as_alternating := by
  intro x hx
  by_contra hx'
  have hxω : x ∉ tsupport ω.as_alternating := by
    intro hxω
    exact hx' (Or.inl hxω)
  have hxη : x ∉ tsupport η.as_alternating := by
    intro hxη
    exact hx' (Or.inr hxη)
  have hω0 : ω.as_alternating =ᶠ[nhds x] 0 :=
    (notMem_tsupport_iff_eventuallyEq).1 hxω
  have hη0 : η.as_alternating =ᶠ[nhds x] 0 :=
    (notMem_tsupport_iff_eventuallyEq).1 hxη
  have hsum :
      (fun y => ω.as_alternating y + η.as_alternating y) =ᶠ[nhds x] 0 :=
    eventuallyEq_zero_add (ω := ω) (η := η) hω0 hη0
  have hxnot : x ∉ tsupport (ω + η).as_alternating :=
    (notMem_tsupport_iff_eventuallyEq).2 (by simpa [SmoothForm.add_apply] using hsum)
  exact hxnot hx

/-- **Hodge Laplacian** Δ on `k`-forms.

`Δω = d(δω) + δ(dω)`.

Note (real model): in this codebase, `⋆` is a fiberwise operator on real 2n-dimensional
forms, so it has degree `k ↦ (2n - k)`. Accordingly, `δ = ⋆ d ⋆` has degree
`k ↦ (k - 1)`, and the `δ d` term is included only for `k < 2n`. -/
noncomputable def laplacian_construct {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    (ω : SmoothForm n X k) : SmoothForm n X k :=
  castForm (by omega) (smoothExtDeriv (codifferential (n := n) (X := X) (k := k) ω)) +
    (if hkn : k = 2 * n then
      0
    else
      castForm (by
        -- In the non-top-degree case, `k < 2n`, so `δ : Ω^{k+1} → Ω^k` has the expected degree.
        have hklt : k < 2 * n := lt_of_le_of_ne hk' hkn
        have hk1 : 1 ≤ 2 * n - k := (Nat.succ_le_iff).2 (Nat.sub_pos_of_lt hklt)
        have hnk : 2 * n - (k + 1) + 1 = 2 * n - k := by
          calc
            2 * n - (k + 1) + 1 = (2 * n - Nat.succ k) + 1 := by
              rw [Nat.add_one k]
            _ = (2 * n - k - 1) + 1 := by
              exact congrArg (fun t => t + 1) (Nat.sub_succ (2 * n) k)
            _ = 2 * n - k := by simpa using (Nat.sub_add_cancel hk1)
        calc
          2 * n - (2 * n - (k + 1) + 1) = 2 * n - (2 * n - k) := by simpa [hnk]
          _ = k := Nat.sub_sub_self hk')
        (codifferential (n := n) (X := X) (k := k + 1) (smoothExtDeriv ω)))

/-- Alias: the Hodge Laplacian Δ = dδ + δd. -/
noncomputable abbrev hodgeLaplacian_construct {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    (ω : SmoothForm n X k) : SmoothForm n X k :=
  laplacian_construct (n := n) (X := X) (k := k) hk hk' ω

/-! ### Linearity of `laplacian_construct` -/

theorem laplacian_construct_zero {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n) :
    laplacian_construct (n := n) (X := X) (k := k) hk hk' 0 = 0 := by
  classical
  by_cases hkn : k = 2 * n
  · subst hkn
    simp [laplacian_construct]
  · simp [laplacian_construct, hkn]

theorem laplacian_construct_add {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    (α β : SmoothForm n X k) :
    laplacian_construct (n := n) (X := X) (k := k) hk hk' (α + β) =
    laplacian_construct (n := n) (X := X) (k := k) hk hk' α +
      laplacian_construct (n := n) (X := X) (k := k) hk hk' β := by
  classical
  by_cases hkn : k = 2 * n
  · subst hkn
    simp [laplacian_construct, smoothExtDeriv_add, castForm_add, add_assoc, add_left_comm, add_comm]
  ·
    simp [laplacian_construct, hkn, smoothExtDeriv_add, castForm_add,
      add_assoc, add_left_comm, add_comm]

theorem laplacian_construct_smul {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    (c : ℂ) (α : SmoothForm n X k) :
    laplacian_construct (n := n) (X := X) (k := k) hk hk' (c • α) =
      c • laplacian_construct (n := n) (X := X) (k := k) hk hk' α := by
  classical
  by_cases hkn : k = 2 * n
  · subst hkn
    simp [laplacian_construct, smoothExtDeriv_smul, castForm_smul, smul_add]
  ·
    simp [laplacian_construct, hkn, smoothExtDeriv_smul, castForm_smul, smul_add]

theorem laplacian_construct_tsupport_subset {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    (ω : SmoothForm n X k) :
    tsupport (laplacian_construct (n := n) (X := X) (k := k) hk hk' ω).as_alternating ⊆
      tsupport ω.as_alternating := by
  by_cases hkn : k = 2 * n
  · subst hkn
    have hleft0 :
        tsupport
            (smoothExtDeriv (n := n) (X := X) (k := k)
              (codifferential (n := n) (X := X) (k := k) ω)).as_alternating ⊆
          tsupport (codifferential (n := n) (X := X) (k := k) ω).as_alternating :=
      smoothExtDeriv_tsupport_subset
        (ω := codifferential (n := n) (X := X) (k := k) ω)
    have hleft1 :
        tsupport (codifferential (n := n) (X := X) (k := k) ω).as_alternating ⊆
          tsupport ω.as_alternating :=
      codifferential_tsupport_subset (ω := ω)
    have hleft :
        tsupport
            (castForm (n := n) (X := X) (by omega)
              (smoothExtDeriv (n := n) (X := X) (k := k)
                (codifferential (n := n) (X := X) (k := k) ω))).as_alternating ⊆
          tsupport ω.as_alternating := by
      simpa [castForm_tsupport_eq] using hleft0.trans hleft1
    have hzero :
        tsupport (0 : SmoothForm n X k).as_alternating ⊆ tsupport ω.as_alternating := by
      intro x hx
      have hxnot : x ∉ tsupport (0 : SmoothForm n X k).as_alternating := by
        have hzero' : (0 : X → FiberAlt n k) =ᶠ[nhds x] 0 := by
          exact Filter.eventuallyEq_of_mem (Filter.univ_mem) (by intro y hy; rfl)
        exact (notMem_tsupport_iff_eventuallyEq).2 hzero'
      exact (hxnot hx).elim
    have hsum :
        tsupport
            (castForm (n := n) (X := X) (by omega)
                (smoothExtDeriv (n := n) (X := X) (k := k)
                  (codifferential (n := n) (X := X) (k := k) ω)) + 0).as_alternating ⊆
          tsupport ω.as_alternating := by
      refine (tsupport_add_subset (ω :=
        castForm (n := n) (X := X) (by omega)
          (smoothExtDeriv (n := n) (X := X) (k := k)
            (codifferential (n := n) (X := X) (k := k) ω))) (η := 0)).trans ?_
      exact Set.union_subset hleft hzero
    simpa [laplacian_construct, hkn] using hsum
  ·
    have hleft0 :
        tsupport
            (smoothExtDeriv (n := n) (X := X) (k := k)
              (codifferential (n := n) (X := X) (k := k) ω)).as_alternating ⊆
          tsupport (codifferential (n := n) (X := X) (k := k) ω).as_alternating :=
      smoothExtDeriv_tsupport_subset
        (ω := codifferential (n := n) (X := X) (k := k) ω)
    have hleft1 :
        tsupport (codifferential (n := n) (X := X) (k := k) ω).as_alternating ⊆
          tsupport ω.as_alternating :=
      codifferential_tsupport_subset (ω := ω)
    have hleft :
        tsupport
            (castForm (n := n) (X := X) (by omega)
              (smoothExtDeriv (n := n) (X := X) (k := k)
                (codifferential (n := n) (X := X) (k := k) ω))).as_alternating ⊆
          tsupport ω.as_alternating := by
      simpa [castForm_tsupport_eq] using hleft0.trans hleft1
    have hright0 :
        tsupport (codifferential (n := n) (X := X) (k := k + 1)
              (smoothExtDeriv (n := n) (X := X) (k := k) ω)).as_alternating ⊆
          tsupport (smoothExtDeriv (n := n) (X := X) (k := k) ω).as_alternating :=
      codifferential_tsupport_subset
        (ω := smoothExtDeriv (n := n) (X := X) (k := k) ω)
    have hright1 :
        tsupport (smoothExtDeriv (n := n) (X := X) (k := k) ω).as_alternating ⊆
          tsupport ω.as_alternating :=
      smoothExtDeriv_tsupport_subset (ω := ω)
    have hcast : 2 * n - (2 * n - (k + 1) + 1) = k := by
      have hklt : k < 2 * n := lt_of_le_of_ne hk' hkn
      have hk1 : 1 ≤ 2 * n - k := (Nat.succ_le_iff).2 (Nat.sub_pos_of_lt hklt)
      have hnk : 2 * n - (k + 1) + 1 = 2 * n - k := by
        calc
          2 * n - (k + 1) + 1 = (2 * n - Nat.succ k) + 1 := by
            rw [Nat.add_one k]
          _ = (2 * n - k - 1) + 1 := by
            exact congrArg (fun t => t + 1) (Nat.sub_succ (2 * n) k)
          _ = 2 * n - k := by simpa using (Nat.sub_add_cancel hk1)
      calc
        2 * n - (2 * n - (k + 1) + 1) = 2 * n - (2 * n - k) := by simpa [hnk]
        _ = k := Nat.sub_sub_self hk'
    have hright :
        tsupport
            (castForm (n := n) (X := X) hcast
              (codifferential (n := n) (X := X) (k := k + 1)
                (smoothExtDeriv (n := n) (X := X) (k := k) ω))).as_alternating ⊆
          tsupport ω.as_alternating := by
      simpa [castForm_tsupport_eq] using hright0.trans hright1
    have hsum :
        tsupport
            (castForm (n := n) (X := X) (by omega)
                (smoothExtDeriv (n := n) (X := X) (k := k)
                  (codifferential (n := n) (X := X) (k := k) ω)) +
              castForm (n := n) (X := X) hcast
                (codifferential (n := n) (X := X) (k := k + 1)
                  (smoothExtDeriv (n := n) (X := X) (k := k) ω))).as_alternating ⊆
          tsupport ω.as_alternating := by
      refine (tsupport_add_subset (ω :=
        castForm (n := n) (X := X) (by omega)
          (smoothExtDeriv (n := n) (X := X) (k := k)
            (codifferential (n := n) (X := X) (k := k) ω)))
        (η :=
          castForm (n := n) (X := X) hcast
            (codifferential (n := n) (X := X) (k := k + 1)
              (smoothExtDeriv (n := n) (X := X) (k := k) ω)))).trans ?_
      exact Set.union_subset hleft hright
    simpa [laplacian_construct, hkn] using hsum

theorem laplacian_construct_hasCompactSupport {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 2 * n)
    (ω : SmoothForm n X k) :
    HasCompactSupport ω.as_alternating →
      HasCompactSupport (laplacian_construct (n := n) (X := X) (k := k) hk hk' ω).as_alternating := by
  intro hcomp
  have hcodiff :
      HasCompactSupport (codifferential (n := n) (X := X) (k := k) ω).as_alternating :=
    codifferential_hasCompactSupport (ω := ω) hcomp
  have hleft :
      HasCompactSupport
          (smoothExtDeriv (n := n) (X := X) (k := k)
              (codifferential (n := n) (X := X) (k := k) ω)).as_alternating :=
    smoothExtDeriv_hasCompactSupport
      (ω := codifferential (n := n) (X := X) (k := k) ω) hcodiff
  have hleft' :
      HasCompactSupport
          (castForm (n := n) (X := X) (by omega)
              (smoothExtDeriv (n := n) (X := X) (k := k)
                (codifferential (n := n) (X := X) (k := k) ω))).as_alternating :=
    castForm_hasCompactSupport (h := by omega)
      (ω := smoothExtDeriv (n := n) (X := X) (k := k)
        (codifferential (n := n) (X := X) (k := k) ω)) hleft
  by_cases hkn : k = 2 * n
  · subst hkn
    have hzero : HasCompactSupport (0 : X → FiberAlt n k) := by
      simpa using (HasCompactSupport.zero : HasCompactSupport (0 : X → FiberAlt n k))
    have hsum :
        HasCompactSupport
          (fun x =>
            (castForm (n := n) (X := X) (by omega)
                (smoothExtDeriv (n := n) (X := X) (k := k)
                  (codifferential (n := n) (X := X) (k := k) ω))).as_alternating x +
              (0 : SmoothForm n X k).as_alternating x) :=
      HasCompactSupport.add hleft' (by simpa using hzero)
    have hsum' :
        HasCompactSupport
          ((castForm (n := n) (X := X) (by omega)
                (smoothExtDeriv (n := n) (X := X) (k := k)
                  (codifferential (n := n) (X := X) (k := k) ω)) + 0).as_alternating) := by
      simpa [SmoothForm.add_apply] using hsum
    simpa [laplacian_construct, hkn] using hsum'
  ·
    have hderiv :
        HasCompactSupport
          (smoothExtDeriv (n := n) (X := X) (k := k) ω).as_alternating :=
      smoothExtDeriv_hasCompactSupport (ω := ω) hcomp
    have hright0 :
        HasCompactSupport
          (codifferential (n := n) (X := X) (k := k + 1)
              (smoothExtDeriv (n := n) (X := X) (k := k) ω)).as_alternating :=
      codifferential_hasCompactSupport
        (ω := smoothExtDeriv (n := n) (X := X) (k := k) ω) hderiv
    have hcast : 2 * n - (2 * n - (k + 1) + 1) = k := by
      -- same arithmetic as in `laplacian_construct`
      have hklt : k < 2 * n := lt_of_le_of_ne hk' hkn
      have hk1 : 1 ≤ 2 * n - k := (Nat.succ_le_iff).2 (Nat.sub_pos_of_lt hklt)
      have hnk : 2 * n - (k + 1) + 1 = 2 * n - k := by
        calc
          2 * n - (k + 1) + 1 = (2 * n - Nat.succ k) + 1 := by
            rw [Nat.add_one k]
          _ = (2 * n - k - 1) + 1 := by
            exact congrArg (fun t => t + 1) (Nat.sub_succ (2 * n) k)
          _ = 2 * n - k := by simpa using (Nat.sub_add_cancel hk1)
      calc
        2 * n - (2 * n - (k + 1) + 1) = 2 * n - (2 * n - k) := by simpa [hnk]
        _ = k := Nat.sub_sub_self hk'
    have hright :
        HasCompactSupport
          (castForm (n := n) (X := X) hcast
              (codifferential (n := n) (X := X) (k := k + 1)
                (smoothExtDeriv (n := n) (X := X) (k := k) ω))).as_alternating :=
      castForm_hasCompactSupport (h := hcast)
        (ω := codifferential (n := n) (X := X) (k := k + 1)
          (smoothExtDeriv (n := n) (X := X) (k := k) ω)) hright0
    have hsum :
        HasCompactSupport
          (fun x =>
            (castForm (n := n) (X := X) (by omega)
                (smoothExtDeriv (n := n) (X := X) (k := k)
                  (codifferential (n := n) (X := X) (k := k) ω))).as_alternating x +
              (castForm (n := n) (X := X) hcast
                (codifferential (n := n) (X := X) (k := k + 1)
                  (smoothExtDeriv (n := n) (X := X) (k := k) ω))).as_alternating x) :=
      HasCompactSupport.add hleft' hright
    have hsum' :
        HasCompactSupport
          ((castForm (n := n) (X := X) (by omega)
                (smoothExtDeriv (n := n) (X := X) (k := k)
                  (codifferential (n := n) (X := X) (k := k) ω)) +
              castForm (n := n) (X := X) hcast
                (codifferential (n := n) (X := X) (k := k + 1)
                  (smoothExtDeriv (n := n) (X := X) (k := k) ω))).as_alternating) := by
      simpa [SmoothForm.add_apply] using hsum
    simpa [laplacian_construct, hkn] using hsum'

/-- Laplacian as a ℂ-linear map (using the current definition of Δ). -/
noncomputable def laplacianLinearMap (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 2 * n) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X k where
  toFun ω := laplacian_construct (n := n) (X := X) (k := k) hk hk' ω
  map_add' := laplacian_construct_add (n := n) (X := X) (k := k) hk hk'
  map_smul' := by
    intro c ω
    simp only [RingHom.id_apply]
    exact laplacian_construct_smul (n := n) (X := X) (k := k) hk hk' c ω
