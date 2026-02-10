import Mathlib
import IndisputableMonolith.ClassicalBridge.Fluids.Galerkin2D
import IndisputableMonolith.ClassicalBridge.Fluids.CPM2D

namespace IndisputableMonolith.ClassicalBridge.Fluids

open Real
open Filter
open Topology
open scoped InnerProductSpace

/-!
# ContinuumLimit2D (Milestone M5)

This file defines a *Lean-checkable pipeline shape* for passing from a family of finite-dimensional
2D Galerkin approximations to a “continuum” limit object.

At this milestone we stay honest about what is and is not formalized:
- we define the relevant objects (an infinite Fourier coefficient state),
- we define the canonical embedding of truncated coefficients into the full Fourier state, and
- we package the analytic compactness/identification steps as explicit hypotheses (no `axiom`, no `sorry`).

The point is to make the dependency graph explicit so that later milestones can progressively
replace hypotheses with proofs.
-/

namespace ContinuumLimit2D

/-!
## Continuum Fourier state on 𝕋²

We model a 2D torus velocity field via its Fourier coefficients:
for each `k : Mode2 = ℤ×ℤ`, a coefficient `VelCoeff = EuclideanSpace ℝ (Fin 2)`.
-/

/-- Full (infinite) Fourier coefficient state for a 2D velocity field on 𝕋². -/
abbrev FourierState2D : Type := Mode2 → VelCoeff

/-!
## Embedding: GalerkinState N → FourierState2D

We extend a truncated state by zero outside the truncation window.
-/

/-- Read a single component coefficient at mode `k` (zero if `k ∉ modes N`). -/
noncomputable def coeffAt {N : ℕ} (u : GalerkinState N) (k : Mode2) (j : Fin 2) : ℝ :=
  if hk : k ∈ modes N then
    -- `k` as an element of the finite index type `(modes N)`
    let k' : (modes N) := ⟨k, hk⟩
    u (k', j)
  else
    0

/-- Extend a truncated Galerkin state by zero to a full Fourier coefficient state. -/
noncomputable def extendByZero {N : ℕ} (u : GalerkinState N) : FourierState2D :=
  fun k =>
    -- Build a 2-vector coefficient from its two components.
    !₂[coeffAt u k ⟨0, by decide⟩, coeffAt u k ⟨1, by decide⟩]

/-!
## Linearity of the zero-extension embedding

We will eventually want to pass (linear) identities from Galerkin trajectories to limits.
For that, it is useful to record that `extendByZero` is a linear map.
-/

lemma coeffAt_add {N : ℕ} (u v : GalerkinState N) (k : Mode2) (j : Fin 2) :
    coeffAt (u + v) k j = coeffAt u k j + coeffAt v k j := by
  classical
  by_cases hk : k ∈ modes N
  · simp [coeffAt, hk]
  · simp [coeffAt, hk]

lemma coeffAt_smul {N : ℕ} (c : ℝ) (u : GalerkinState N) (k : Mode2) (j : Fin 2) :
    coeffAt (c • u) k j = c * coeffAt u k j := by
  classical
  by_cases hk : k ∈ modes N
  · simp [coeffAt, hk]
  · simp [coeffAt, hk]

lemma extendByZero_add {N : ℕ} (u v : GalerkinState N) :
    extendByZero (u + v) = extendByZero u + extendByZero v := by
  classical
  funext k
  ext j
  fin_cases j <;> simp [extendByZero, coeffAt_add]

lemma extendByZero_smul {N : ℕ} (c : ℝ) (u : GalerkinState N) :
    extendByZero (c • u) = c • (extendByZero u) := by
  classical
  funext k
  ext j
  fin_cases j <;> simp [extendByZero, coeffAt_smul]

lemma extendByZero_neg {N : ℕ} (u : GalerkinState N) :
    extendByZero (-u) = -extendByZero u := by
  classical
  -- `-u = (-1) • u` and `extendByZero` is linear.
  simpa [neg_one_smul] using (extendByZero_smul (N := N) (-1) u)

/-- `extendByZero` packaged as a linear map. -/
noncomputable def extendByZeroLinear (N : ℕ) : GalerkinState N →ₗ[ℝ] FourierState2D :=
  { toFun := extendByZero
    map_add' := extendByZero_add (N := N)
    map_smul' := by
      intro c u
      -- `simp` expects `c • x`; our lemma is stated in that form.
      simpa using (extendByZero_smul (N := N) c u) }

/-- `extendByZero` as a *continuous* linear map.

This is available because `GalerkinState N` is finite-dimensional, hence every linear map out of it
is continuous. -/
noncomputable def extendByZeroCLM (N : ℕ) : GalerkinState N →L[ℝ] FourierState2D :=
  LinearMap.toContinuousLinearMap (extendByZeroLinear N)

/-!
## Divergence-free structure (Fourier side) and limit stability

A structural property we can pass to the limit using only modewise convergence is a closed,
linear constraint such as “divergence-free in Fourier variables”:

`k₁ * û₁(t,k) + k₂ * û₂(t,k) = 0` for every mode `k`.
-/

/-- Real Fourier-side divergence constraint for a single mode. -/
noncomputable def divConstraint (k : Mode2) (v : VelCoeff) : ℝ :=
  (k.1 : ℝ) * v (0 : Fin 2) + (k.2 : ℝ) * v (1 : Fin 2)

/-- Fourier-side divergence-free predicate (modewise, at a fixed time). -/
def IsDivergenceFree (u : FourierState2D) : Prop :=
  ∀ k : Mode2, divConstraint k (u k) = 0

/-- Divergence-free predicate for a time-dependent Fourier trajectory. -/
def IsDivergenceFreeTraj (u : ℝ → FourierState2D) : Prop :=
  ∀ t : ℝ, ∀ k : Mode2, divConstraint k ((u t) k) = 0

lemma divConstraint_continuous (k : Mode2) : Continuous fun v : VelCoeff => divConstraint k v := by
  have h0 : Continuous fun v : VelCoeff => v (0 : Fin 2) := by
    simpa using
      (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2))
  have h1 : Continuous fun v : VelCoeff => v (1 : Fin 2) := by
    simpa using
      (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2))
  simpa [divConstraint] using ((continuous_const.mul h0).add (continuous_const.mul h1))

/-!
## Linear Stokes/heat mild form (Fourier side) and limit stability

As a next step toward a real PDE statement, we can talk about the *linear* (viscous) dynamics.
On the Fourier side, the Stokes/heat semigroup acts diagonally:

`û(t,k) = exp(-ν |k|^2 t) • û(0,k)`.

This is still not Navier–Stokes, but it is a concrete PDE-like identity that can be passed to the
limit using only modewise convergence (no compactness beyond that).
-/

/-- Fourier-side heat/Stokes factor `e^{-ν|k|^2 t}`. -/
noncomputable def heatFactor (ν : ℝ) (t : ℝ) (k : Mode2) : ℝ :=
  Real.exp (-ν * kSq k * t)

/-- Mild Stokes/heat solution in Fourier coefficients (modewise, for `t ≥ 0`). -/
def IsStokesMildTraj (ν : ℝ) (u : ℝ → FourierState2D) : Prop :=
  ∀ t ≥ 0, ∀ k : Mode2, (u t) k = (heatFactor ν t k) • (u 0) k

/-- Differential (within `t ≥ 0`) Stokes/heat equation in Fourier coefficients (modewise).

This is a slightly more “PDE-like” statement than the mild form: for each fixed mode `k`,
the coefficient trajectory satisfies

`d/dt u(t,k) = -(ν |k|^2) • u(t,k)`

as a derivative **within** the half-line `[0,∞)`. -/
def IsStokesODETraj (ν : ℝ) (u : ℝ → FourierState2D) : Prop :=
  ∀ t ≥ 0, ∀ k : Mode2,
    HasDerivWithinAt (fun s : ℝ => (u s) k) (-(ν * kSq k) • (u t) k) (Set.Ici (0 : ℝ)) t

namespace IsStokesMildTraj

/-- Mild Stokes/heat identity implies the corresponding differential equation (within `t ≥ 0`). -/
theorem stokesODE {ν : ℝ} {u : ℝ → FourierState2D} (h : IsStokesMildTraj ν u) :
    IsStokesODETraj ν u := by
  intro t ht k
  -- Let `a = u(0,k)` so the mild formula reads `u(s,k) = exp(-ν|k|^2 s) • a` for `s ≥ 0`.
  let a : VelCoeff := (u 0) k

  -- Derivative of the scalar heat factor.
  have hlin : HasDerivAt (fun s : ℝ => (-ν * kSq k) * s) (-ν * kSq k) t := by
    simpa [mul_assoc] using (hasDerivAt_id t).const_mul (-ν * kSq k)
  have hscalar :
      HasDerivAt (fun s : ℝ => heatFactor ν s k)
        (heatFactor ν t k * (-ν * kSq k)) t := by
    -- `d/ds exp(g(s)) = exp(g(s)) * g'(s)` with `g(s) = (-ν|k|^2) * s`.
    have hexp :
        HasDerivAt (fun s : ℝ => Real.exp ((-ν * kSq k) * s))
          (Real.exp ((-ν * kSq k) * t) * (-ν * kSq k)) t :=
      (Real.hasDerivAt_exp ((-ν * kSq k) * t)).comp t hlin
    simpa [heatFactor, mul_assoc] using hexp
  have hscalarW :
      HasDerivWithinAt (fun s : ℝ => heatFactor ν s k)
        (heatFactor ν t k * (-ν * kSq k)) (Set.Ici (0 : ℝ)) t :=
    hscalar.hasDerivWithinAt

  -- Differentiate `s ↦ heatFactor ν s k • a` within `[0,∞)`.
  have hform :
      HasDerivWithinAt (fun s : ℝ => (heatFactor ν s k) • a)
        ((heatFactor ν t k * (-ν * kSq k)) • a) (Set.Ici (0 : ℝ)) t :=
    hscalarW.smul_const a

  -- Replace the formula by `u` using the mild identity on the domain `[0,∞)`.
  have huEq : ∀ s ∈ Set.Ici (0 : ℝ), (fun s : ℝ => (u s) k) s = (fun s : ℝ => (heatFactor ν s k) • a) s := by
    intro s hs
    -- `hs : 0 ≤ s`
    simpa [a] using (h s hs k)
  have huEq_t : (fun s : ℝ => (u s) k) t = (fun s : ℝ => (heatFactor ν s k) • a) t := by
    simpa [a] using (h t ht k)

  have huDeriv :
      HasDerivWithinAt (fun s : ℝ => (u s) k) ((heatFactor ν t k * (-ν * kSq k)) • a)
        (Set.Ici (0 : ℝ)) t :=
    hform.congr huEq huEq_t

  -- Simplify the derivative into `-(ν|k|^2) • u(t,k)`.
  have hsimp :
      ((heatFactor ν t k * (-ν * kSq k)) • a) = (-(ν * kSq k)) • ((u t) k) := by
    -- Use commutativity of real multiplication to flip the order, then `mul_smul`.
    have hut : (u t) k = (heatFactor ν t k) • a := by
      simpa [a] using (h t ht k)
    -- Rewrite to match `mul_smul` and then substitute `hut`.
    calc
      (heatFactor ν t k * (-ν * kSq k)) • a
          = ((-ν * kSq k) * heatFactor ν t k) • a := by
              simp [mul_comm, mul_assoc]
      _ = (-ν * kSq k) • ((heatFactor ν t k) • a) := by
              simp [mul_smul]
      _ = (-(ν * kSq k)) • ((heatFactor ν t k) • a) := by ring_nf
      _ = (-(ν * kSq k)) • ((u t) k) := by simp [hut]

  -- `simp` may rewrite `heatFactor * (-ν*kSq)` as `-(heatFactor * (ν*kSq))`, so we also register
  -- a simp-friendly variant with the outer negation.
  have hsimp_neg :
      -((heatFactor ν t k * (ν * kSq k)) • a) = (-(ν * kSq k)) • ((u t) k) := by
    -- Move the `-` inside as `(-1) • _` and simplify using `hsimp`.
    have : (heatFactor ν t k * (-ν * kSq k)) • a = -((heatFactor ν t k * (ν * kSq k)) • a) := by
      -- scalar arithmetic in `ℝ` + `(-r) • a = -(r • a)`
      calc
        (heatFactor ν t k * (-ν * kSq k)) • a
            = (-(heatFactor ν t k * (ν * kSq k))) • a := by ring_nf
        _ = -((heatFactor ν t k * (ν * kSq k)) • a) := by
            simp [neg_smul]
    -- Now rewrite and finish.
    simpa [this] using hsimp

  simpa [IsStokesODETraj, hsimp_neg] using huDeriv

end IsStokesMildTraj

/-!
## Galerkin → Fourier coefficient dynamics (modewise ODE, with nonlinearity)

This is the first genuinely “Navier–Stokes shaped” bridge lemma: if a Galerkin trajectory satisfies
the finite-dimensional ODE `u' = νΔu - B(u,u)`, then every Fourier mode of its zero-extension
satisfies the corresponding modewise ODE with a forcing given by the zero-extended nonlinear term.
-/

lemma extendByZero_laplacianCoeff {N : ℕ} (u : GalerkinState N) (k : Mode2) :
    (extendByZero (laplacianCoeff (N := N) u)) k = (-kSq k) • (extendByZero u) k := by
  classical
  by_cases hk : k ∈ modes N
  · ext j
    fin_cases j <;> simp [extendByZero, coeffAt, hk, laplacianCoeff]
  · ext j
    fin_cases j <;> simp [extendByZero, coeffAt, hk]

lemma hasDerivAt_extendByZero_apply {N : ℕ} (k : Mode2)
    (u : ℝ → GalerkinState N) (u' : GalerkinState N) {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s : ℝ => (extendByZero (u s)) k) ((extendByZero u') k) t := by
  classical
  -- A constant continuous linear map: project the `k`-th Fourier coefficient after zero-extension.
  let L : GalerkinState N →L[ℝ] VelCoeff :=
    (ContinuousLinearMap.proj k).comp (extendByZeroCLM (N := N))
  have hL : HasDerivAt (fun _ : ℝ => L) 0 t := by
    simpa using (hasDerivAt_const (x := t) (c := L))
  -- Differentiate `s ↦ L (u s)`.
  have h := HasDerivAt.clm_apply (c := fun _ : ℝ => L) (c' := (0 : GalerkinState N →L[ℝ] VelCoeff))
    (u := u) (u' := u') (x := t) hL hu
  -- Unfold `L` back to `extendByZero` + evaluation at `k`.
  simpa [L, extendByZeroCLM] using h

theorem galerkinNS_hasDerivAt_extendByZero_mode {N : ℕ} (ν : ℝ) (B : ConvectionOp N)
    (u : ℝ → GalerkinState N) (k : Mode2) {t : ℝ}
    (hu : HasDerivAt u (galerkinNSRHS (N := N) ν B (u t)) t) :
    HasDerivAt (fun s : ℝ => (extendByZero (u s)) k)
      ((ν * (-kSq k)) • (extendByZero (u t)) k - (extendByZero (B (u t) (u t))) k) t := by
  -- Start from the generic differentiation-through-zero-extension lemma.
  have h0 :
      HasDerivAt (fun s : ℝ => (extendByZero (u s)) k)
        ((extendByZero (galerkinNSRHS (N := N) ν B (u t))) k) t :=
    hasDerivAt_extendByZero_apply (N := N) k u (galerkinNSRHS (N := N) ν B (u t)) hu
  -- Simplify the RHS using linearity of `extendByZero` and the diagonal Laplacian.
  -- `extendByZero (ν•Δu - B(u,u)) = ν•extendByZero(Δu) - extendByZero(B(u,u))`
  have hR :
      (extendByZero (galerkinNSRHS (N := N) ν B (u t)) k)
        = (ν * (-kSq k)) • (extendByZero (u t)) k - (extendByZero (B (u t) (u t))) k := by
    -- Push `extendByZero` through the RHS definition.
    simp [galerkinNSRHS, extendByZero_smul, extendByZero_add, extendByZero_neg,
      extendByZero_laplacianCoeff, sub_eq_add_neg, mul_smul]
  -- Rewrite the derivative statement with the simplified RHS.
  simpa [hR] using h0

/-!
## A derived bound: single coefficient ≤ global norm

Even before doing any PDE analysis, we can prove a simple but useful fact:
the norm of one Fourier coefficient (after zero-extension) is bounded by the
global Euclidean norm of the truncated Galerkin state.
-/

lemma norm_extendByZero_le {N : ℕ} (u : GalerkinState N) (k : Mode2) :
    ‖(extendByZero u) k‖ ≤ ‖u‖ := by
  classical
  by_cases hk : k ∈ modes N
  ·
    have hext :
        (extendByZero u) k =
          !₂[u (⟨k, hk⟩, (⟨0, by decide⟩ : Fin 2)),
             u (⟨k, hk⟩, (⟨1, by decide⟩ : Fin 2))] := by
      simp [extendByZero, coeffAt, hk]

    have hsq_ext :
        ‖(extendByZero u) k‖ ^ 2 =
          ‖u (⟨k, hk⟩, (⟨0, by decide⟩ : Fin 2))‖ ^ 2
            + ‖u (⟨k, hk⟩, (⟨1, by decide⟩ : Fin 2))‖ ^ 2 := by
      -- For `Fin 2`, `EuclideanSpace.norm_sq_eq` expands to the sum of the two coordinate squares.
      simp [hext, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

    have hnorm_u : ‖u‖ ^ 2 = ∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq]

    -- The 2-coordinate sum is bounded by the full coordinate sum.
    have hcoord_le :
        (‖u (⟨k, hk⟩, (⟨0, by decide⟩ : Fin 2))‖ ^ 2
            + ‖u (⟨k, hk⟩, (⟨1, by decide⟩ : Fin 2))‖ ^ 2)
          ≤ (∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2) := by
      let k' : (modes N) := ⟨k, hk⟩
      let s : Finset ((modes N) × Fin 2) :=
        insert (k', (⟨0, by decide⟩ : Fin 2)) ({(k', (⟨1, by decide⟩ : Fin 2))} : Finset ((modes N) × Fin 2))
      have hs : s ⊆ (Finset.univ : Finset ((modes N) × Fin 2)) := by
        intro x hx
        simp
      have hsum :
          (‖u (k', (⟨0, by decide⟩ : Fin 2))‖ ^ 2 + ‖u (k', (⟨1, by decide⟩ : Fin 2))‖ ^ 2)
            = (∑ kc ∈ s, ‖u kc‖ ^ 2) := by
        simp [s]
      have hle : (∑ kc ∈ s, ‖u kc‖ ^ 2) ≤ (∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2) := by
        have hle' :
            (∑ kc ∈ s, ‖u kc‖ ^ 2)
              ≤ (∑ kc ∈ (Finset.univ : Finset ((modes N) × Fin 2)), ‖u kc‖ ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hs ?_
          intro kc _hkc _hknot
          exact sq_nonneg ‖u kc‖
        simpa using hle'
      calc
        (‖u (k', (⟨0, by decide⟩ : Fin 2))‖ ^ 2 + ‖u (k', (⟨1, by decide⟩ : Fin 2))‖ ^ 2)
            = (∑ kc ∈ s, ‖u kc‖ ^ 2) := hsum
        _ ≤ (∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2) := hle

    have hsq_le : ‖(extendByZero u) k‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      calc
        ‖(extendByZero u) k‖ ^ 2
            = (‖u (⟨k, hk⟩, (⟨0, by decide⟩ : Fin 2))‖ ^ 2
                + ‖u (⟨k, hk⟩, (⟨1, by decide⟩ : Fin 2))‖ ^ 2) := hsq_ext
        _ ≤ (∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2) := hcoord_le
        _ = ‖u‖ ^ 2 := by simp [hnorm_u]

    exact le_of_sq_le_sq hsq_le (norm_nonneg u)
  ·
    -- Outside the truncation window the coefficient is zero, so the bound is trivial.
    have hnorm : ‖(extendByZero u) k‖ = 0 := by
      simp [extendByZero, coeffAt, hk]
    simp [hnorm, norm_nonneg u]

/-!
## Compactness + identification as explicit hypotheses
-/

/-- Hypothesis: uniform-in-`N` bounds for a *family* of Galerkin trajectories `uN`.

In a real proof this would come from:
- discrete energy/enstrophy inequalities,
- CPM coercivity/dispersion bounds, and
- compactness tools (Aubin–Lions / Banach–Alaoglu / etc.).
-/
structure UniformBoundsHypothesis where
  /-- Discrete Galerkin trajectories at each truncation level `N`. -/
  uN : (N : ℕ) → ℝ → GalerkinState N
  /-- A global (in time, and uniform in `N`) bound. -/
  B : ℝ
  B_nonneg : 0 ≤ B
  /-- Uniform bound: for all `N` and all `t ≥ 0`, `‖uN N t‖ ≤ B`. -/
  bound : ∀ N : ℕ, ∀ t ≥ 0, ‖uN N t‖ ≤ B

/-- Build `UniformBoundsHypothesis` from the *viscous* Galerkin energy estimate, provided we have
an initial uniform bound `‖uN N 0‖ ≤ B` across all truncation levels.
-/
noncomputable def UniformBoundsHypothesis.ofViscous
    (ν : ℝ) (hν : 0 ≤ ν)
    (Bop : (N : ℕ) → ConvectionOp N)
    (HB : ∀ N : ℕ, EnergySkewHypothesis (Bop N))
    (u : (N : ℕ) → ℝ → GalerkinState N)
    (hu : ∀ N : ℕ, ∀ t : ℝ, HasDerivAt (u N) (galerkinNSRHS ν (Bop N) ((u N) t)) t)
    (B : ℝ) (B_nonneg : 0 ≤ B)
    (h0 : ∀ N : ℕ, ‖u N 0‖ ≤ B) :
    UniformBoundsHypothesis :=
  { uN := u
    B := B
    B_nonneg := B_nonneg
    bound := by
      intro N t ht
      have hNt : ‖u N t‖ ≤ ‖u N 0‖ :=
        viscous_norm_bound_from_initial (N := N) ν hν (Bop N) (HB N) (u N) (hu N) t ht
      exact le_trans hNt (h0 N) }

/-- Hypothesis: existence of a limit Fourier trajectory and convergence from the approximants. -/
structure ConvergenceHypothesis (H : UniformBoundsHypothesis) where
  /-- Candidate limit (time → full Fourier coefficients). -/
  u : ℝ → FourierState2D
  /-- Pointwise (mode-by-mode) convergence of the zero-extended Galerkin coefficients. -/
  converges : ∀ t : ℝ, ∀ k : Mode2,
    Tendsto (fun N : ℕ => (extendByZero (H.uN N t)) k) atTop (𝓝 ((u t) k))

namespace ConvergenceHypothesis

/-- Derived fact: if the approximants are uniformly bounded in the Galerkin norm for `t ≥ 0`,
then the limit coefficients inherit the same bound (by closedness of `closedBall`). -/
theorem coeff_bound_of_uniformBounds {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) :
    ∀ t ≥ 0, ∀ k : Mode2, ‖(HC.u t) k‖ ≤ H.B := by
  intro t ht k
  -- Put every approximant coefficient inside the closed ball of radius `B`.
  have hmem :
      ∀ N : ℕ, (extendByZero (H.uN N t) k) ∈ Metric.closedBall (0 : VelCoeff) H.B := by
    intro N
    have h1 : ‖(extendByZero (H.uN N t)) k‖ ≤ ‖H.uN N t‖ :=
      norm_extendByZero_le (u := H.uN N t) (k := k)
    have h2 : ‖H.uN N t‖ ≤ H.B := H.bound N t ht
    have h3 : ‖(extendByZero (H.uN N t)) k‖ ≤ H.B := le_trans h1 h2
    -- `Metric.mem_closedBall` is `dist ≤ radius`, and `dist x 0 = ‖x‖`.
    simpa [Metric.mem_closedBall, dist_zero_right] using h3

  have hmem_event :
      (∀ᶠ N : ℕ in atTop, (extendByZero (H.uN N t) k) ∈ Metric.closedBall (0 : VelCoeff) H.B) :=
    Filter.Eventually.of_forall hmem

  have hlim_mem :
      (HC.u t) k ∈ Metric.closedBall (0 : VelCoeff) H.B :=
    IsClosed.mem_of_tendsto (b := atTop) Metric.isClosed_closedBall (HC.converges t k) hmem_event

  have : dist ((HC.u t) k) (0 : VelCoeff) ≤ H.B :=
    (Metric.mem_closedBall).1 hlim_mem

  simpa [dist_zero_right] using this

/-- If the approximants satisfy the (Fourier) divergence constraint at a fixed `t,k`, then so does
the limit coefficient (by continuity + uniqueness of limits in `ℝ`). -/
theorem divConstraint_eq_zero_of_forall {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (t : ℝ) (k : Mode2)
    (hDF : ∀ N : ℕ, divConstraint k ((extendByZero (H.uN N t)) k) = 0) :
    divConstraint k ((HC.u t) k) = 0 := by
  -- Push convergence through the continuous map `divConstraint k`.
  have hT :
      Tendsto (fun N : ℕ => divConstraint k ((extendByZero (H.uN N t)) k)) atTop
        (𝓝 (divConstraint k ((HC.u t) k))) := by
    have hcont : Continuous (fun v : VelCoeff => divConstraint k v) := divConstraint_continuous k
    have hcontT :
        Tendsto (fun v : VelCoeff => divConstraint k v) (𝓝 ((HC.u t) k))
          (𝓝 (divConstraint k ((HC.u t) k))) :=
      hcont.tendsto ((HC.u t) k)
    exact hcontT.comp (HC.converges t k)

  -- The sequence is constantly 0 by assumption.
  have heq : (fun N : ℕ => divConstraint k ((extendByZero (H.uN N t)) k)) = fun _ : ℕ => (0 : ℝ) := by
    funext N
    simpa using (hDF N)

  have hT0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (divConstraint k ((HC.u t) k))) := by
    simpa [heq] using hT
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds

  exact tendsto_nhds_unique hT0 hconst

/-- Divergence-free passes to the limit under modewise convergence, assuming each approximant is
divergence-free (in the Fourier-side sense) at every time. -/
theorem divFree_of_forall {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (hDF : ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2, divConstraint k ((extendByZero (H.uN N t)) k) = 0) :
    IsDivergenceFreeTraj HC.u := by
  intro t k
  exact divConstraint_eq_zero_of_forall (HC := HC) (t := t) (k := k) (hDF := fun N => hDF N t k)

/-- Mild Stokes/heat identity passes to the limit under modewise convergence,
assuming it holds for every approximant (modewise, for `t ≥ 0`). -/
theorem stokesMild_of_forall {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) (ν : ℝ)
    (hMild :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) = (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) :
    IsStokesMildTraj ν HC.u := by
  intro t ht k
  -- convergence at time t and at time 0
  have hconv_t : Tendsto (fun N : ℕ => extendByZero (H.uN N t) k) atTop (nhds ((HC.u t) k)) :=
    HC.converges t k
  have hconv_0 : Tendsto (fun N : ℕ => extendByZero (H.uN N 0) k) atTop (nhds ((HC.u 0) k)) :=
    HC.converges 0 k
  -- push convergence at time 0 through the continuous map `v ↦ heatFactor • v`
  have hsmul :
      Tendsto (fun N : ℕ => (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) atTop
        (nhds ((heatFactor ν t k) • ((HC.u 0) k))) := by
    have hcont : Continuous fun v : VelCoeff => (heatFactor ν t k) • v := continuous_const_smul _
    exact (hcont.tendsto ((HC.u 0) k)).comp hconv_0
  -- but the two sequences are equal for all N (by hypothesis), hence have the same limit
  have hEq :
      (fun N : ℕ => extendByZero (H.uN N t) k)
        =ᶠ[atTop] (fun N : ℕ => (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    exact hMild N t ht k
  -- uniqueness of limits in a T2 space
  have : (HC.u t) k = (heatFactor ν t k) • ((HC.u 0) k) :=
    tendsto_nhds_unique_of_eventuallyEq hconv_t hsmul hEq
  simpa using this

end ConvergenceHypothesis

/-- Convenience constructor: if each coefficient sequence is *eventually equal* to the corresponding
limit coefficient, then it tends to that limit. -/
noncomputable def ConvergenceHypothesis.ofEventuallyEq
    (H : UniformBoundsHypothesis)
    (u : ℝ → FourierState2D)
    (heq :
      ∀ t : ℝ, ∀ k : Mode2,
        (fun N : ℕ => (extendByZero (H.uN N t)) k) =ᶠ[atTop] (fun _ : ℕ => (u t) k)) :
    ConvergenceHypothesis H :=
  { u := u
    converges := by
      intro t k
      have hconst : Tendsto (fun _ : ℕ => (u t) k) atTop (𝓝 ((u t) k)) :=
        tendsto_const_nhds
      exact (tendsto_congr' (heq t k)).2 hconst }

/-- Hypothesis: the limit object satisfies the intended PDE identity (kept abstract here). -/
structure IdentificationHypothesis {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) where
  /-- A (later: concrete) solution concept for 2D Navier–Stokes on the torus. -/
  IsSolution : (ℝ → FourierState2D) → Prop
  /-- Proof that the limit trajectory satisfies the chosen solution concept. -/
  isSolution : IsSolution HC.u

namespace IdentificationHypothesis

/-- Trivial identification constructor: choose `IsSolution := True`. -/
def trivial {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) :
    IdentificationHypothesis HC :=
  { IsSolution := fun _ => True
    isSolution := by trivial }

/-- Concrete (but still minimal) identification: define `IsSolution u` to mean the limit coefficients
are uniformly bounded by the Galerkin bound `H.B` for `t ≥ 0`.

This is **provable** from `UniformBoundsHypothesis` + modewise convergence (no extra analytic input),
via `ConvergenceHypothesis.coeff_bound_of_uniformBounds`.
-/
def coeffBound {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) :
    IdentificationHypothesis HC :=
  { IsSolution := fun u => ∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B
    isSolution := by
      intro t ht k
      simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k) }

/-- Identification constructor: coefficient bound + divergence-free (Fourier-side).

The coefficient bound part is proved from `UniformBoundsHypothesis` + convergence.
The divergence-free part is proved from the extra assumption that *each approximant* is divergence-free.
-/
def divFreeCoeffBound {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (hDF : ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2, divConstraint k ((extendByZero (H.uN N t)) k) = 0) :
    IdentificationHypothesis HC :=
  { IsSolution := fun u =>
      (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B) ∧ IsDivergenceFreeTraj u
    isSolution := by
      refine ⟨?_, ?_⟩
      · intro t ht k
        simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k)
      · intro t k
        exact ConvergenceHypothesis.divConstraint_eq_zero_of_forall (HC := HC) (t := t) (k := k)
          (hDF := fun N => hDF N t k) }

/-- Identification constructor: coefficient bound + (linear) Stokes/heat mild identity.

The bound part is proved from `UniformBoundsHypothesis` + convergence.
The mild Stokes identity is proved from the extra assumption that it holds for every approximant. -/
def stokesMildCoeffBound {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) (ν : ℝ)
    (hMild :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) = (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) :
    IdentificationHypothesis HC :=
  { IsSolution := fun u =>
      (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B) ∧ IsStokesMildTraj ν u
    isSolution := by
      refine ⟨?_, ?_⟩
      · intro t ht k
        simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k)
      · exact ConvergenceHypothesis.stokesMild_of_forall (HC := HC) (ν := ν) hMild }

end IdentificationHypothesis

/-!
## The milestone theorem: “uniform bounds + convergence + identification ⇒ continuum solution”

At this stage the theorem returns the packaged limit object together with its claimed properties.
-/

theorem continuum_limit_exists
    (H : UniformBoundsHypothesis)
    (HC : ConvergenceHypothesis H)
    (HI : IdentificationHypothesis HC) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2, Tendsto (fun N : ℕ => (extendByZero (H.uN N t)) k) atTop (𝓝 ((u t) k)))
        ∧ HI.IsSolution u
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B) := by
  refine ⟨HC.u, HC.converges, ?_, ?_⟩
  · simpa using HI.isSolution
  · intro t ht k
    simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k)

end ContinuumLimit2D

end IndisputableMonolith.ClassicalBridge.Fluids
