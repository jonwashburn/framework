import Hodge.Analytic.Laplacian.Codifferential

/-!
# Hodge Laplacian Δ (skeleton / off proof track)

This module introduces a compile-stable interface for the **Hodge Laplacian**
\(\Delta = d\delta + \delta d\).

In the current repository architecture:
- `d` is implemented as `smoothExtDeriv` in `Hodge/Analytic/Forms.lean`.
- `⋆` is wired via `HodgeStarData.fromFiber` (see `Hodge/Analytic/Norms.lean`), and is now
  nontrivial at the fiber level.

This file is **off proof track** unless explicitly imported.
-/

noncomputable section

open Classical

namespace Hodge
namespace HodgeLaplacian

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

/-- **Hodge Laplacian** Δ on `k`-forms.

In a full implementation this should be:

`Δω = d(δω) + δ(dω)`.

This file keeps the *structurally correct* formula for Δ so downstream files can be written
against the intended API.

Note (repo-specific model): in this codebase, `⋆` (see `Hodge/Analytic/Norms.lean`) is a fiberwise
operator on complex-linear forms, so it has degree `k ↦ (n-k)`. Accordingly, `δ = ±⋆d⋆` has degree
`k ↦ (k-1)` only in the range `k ≤ n`.  The Laplacian is therefore packaged here with hypotheses
`1 ≤ k` and `k ≤ n`. -/
noncomputable def laplacian_construct {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n)
    (ω : SmoothForm n X k) : SmoothForm n X k :=
  -- Δω = d(δω) + δ(dω)
  castForm (by omega) (smoothExtDeriv (Codifferential.codifferential (n := n) (X := X) (k := k) ω)) +
    (if hkn : k = n then
      0
    else
      castForm (by
        -- In the non-top-degree case, `k < n`, so `δ : Ω^{k+1} → Ω^k` has the expected degree.
        have hklt : k < n := lt_of_le_of_ne hk' hkn
        have hk1 : 1 ≤ n - k := (Nat.succ_le_iff).2 (Nat.sub_pos_of_lt hklt)
        have hnk : n - (k + 1) + 1 = n - k := by
          -- `n - (k+1) = n - k - 1`, and `(n-k)-1+1 = n-k` since `n-k ≥ 1`.
          calc
            n - (k + 1) + 1 = (n - Nat.succ k) + 1 := by
              -- Avoid `simp` loops on `Nat.add_one`/`Nat.succ_eq_add_one`.
              rw [Nat.add_one k]
            _ = (n - k - 1) + 1 := by
              -- `Nat.sub_succ : n - Nat.succ k = n - k - 1`
              exact congrArg (fun t => t + 1) (Nat.sub_succ n k)
            _ = n - k := by simpa using (Nat.sub_add_cancel hk1)
        -- Now finish by rewriting to `n - (n - k) = k`.
        calc
          n - (n - (k + 1) + 1) = n - (n - k) := by simpa [hnk]
          _ = k := Nat.sub_sub_self hk')
        (Codifferential.codifferential (n := n) (X := X) (k := k + 1) (smoothExtDeriv ω)))

/-- Alias (naming used in the operational plan): the Hodge Laplacian Δ = dδ + δd. -/
noncomputable abbrev hodgeLaplacian_construct {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n)
    (ω : SmoothForm n X k) : SmoothForm n X k :=
  laplacian_construct (n := n) (X := X) (k := k) hk hk' ω

/-! ### Linearity of laplacian_construct -/

/-- Laplacian of zero is zero. -/
theorem laplacian_construct_zero {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n) :
    laplacian_construct (n := n) (X := X) (k := k) hk hk' 0 = 0 := by
  classical
  by_cases hkn : k = n
  · subst hkn
    simp [laplacian_construct, Codifferential.codifferential_zero, smoothExtDeriv_zero]
  · simp [laplacian_construct, hkn, Codifferential.codifferential_zero, smoothExtDeriv_zero]

/-- Laplacian is additive. -/
theorem laplacian_construct_add {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n)
    (α β : SmoothForm n X k) :
    laplacian_construct hk hk' (α + β) =
    laplacian_construct hk hk' α + laplacian_construct hk hk' β := by
  classical
  by_cases hkn : k = n
  · subst hkn
    simp [laplacian_construct, Codifferential.codifferential_add, smoothExtDeriv_add, castForm_add,
      add_assoc, add_left_comm, add_comm]
  ·
    simp [laplacian_construct, hkn, Codifferential.codifferential_add, smoothExtDeriv_add, castForm_add,
      add_assoc, add_left_comm, add_comm]

/-- Laplacian respects ℂ-scalar multiplication. -/
theorem laplacian_construct_smul {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n)
    (c : ℂ) (α : SmoothForm n X k) :
    laplacian_construct hk hk' (c • α) = c • laplacian_construct hk hk' α := by
  classical
  by_cases hkn : k = n
  · subst hkn
    simp [laplacian_construct, Codifferential.codifferential_smul, smoothExtDeriv_smul, castForm_smul,
      add_assoc, add_left_comm, add_comm, smul_add]
  ·
    simp [laplacian_construct, hkn, Codifferential.codifferential_smul, smoothExtDeriv_smul, castForm_smul,
      add_assoc, add_left_comm, add_comm, smul_add]

/-- Laplacian as a ℂ-linear map (using the current definition of Δ).

Linearity is proved structurally from linearity of d and δ. -/
noncomputable def laplacianLinearMap (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ n) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X k where
  toFun ω := laplacian_construct (n := n) (X := X) (k := k) hk hk' ω
  map_add' := laplacian_construct_add hk hk'
  map_smul' := fun c ω => by
    simp only [RingHom.id_apply]
    exact laplacian_construct_smul hk hk' c ω

-- The analytic identification of `Δ = dδ + δd` with an elliptic operator and the full Hodge theory
-- consequences (e.g. harmonic decomposition) are not developed here.

end HodgeLaplacian
end Hodge
