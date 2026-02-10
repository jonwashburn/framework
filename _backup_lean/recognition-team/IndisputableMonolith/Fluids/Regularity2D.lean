import IndisputableMonolith.ClassicalBridge.Fluids.Galerkin2D
import IndisputableMonolith.ClassicalBridge.Fluids.LNALSemantics
import IndisputableMonolith.ClassicalBridge.Fluids.Simulation2D
import IndisputableMonolith.ClassicalBridge.Fluids.CPM2D
import IndisputableMonolith.ClassicalBridge.Fluids.ContinuumLimit2D

namespace IndisputableMonolith.ClassicalBridge.Fluids

/-!
# Regularity2D (Milestone M6)

This file provides the **top-level composition theorem** for the 2D pipeline:

Galerkin2D (M1) + LNAL encoding/semantics (M2) + one-step simulation (M3) +
CPM instantiation (M4) + continuum limit packaging (M5)
⇒ an abstract “continuum solution exists” conclusion.

At this milestone the goal is architectural: we make the dependency graph explicit and
compose the previously packaged hypotheses **without** using `sorry` or `axiom`.
-/

namespace Regularity2D

open ContinuumLimit2D

/-!
## Master hypothesis: all ingredients of the 2D pipeline
-/

structure RSNS2DPipelineHypothesis where
  /-- Uniform-in-`N` bounds for the Galerkin family. -/
  Hbounds : UniformBoundsHypothesis
  /-- Convergence to a limit Fourier trajectory. -/
  Hconv : ConvergenceHypothesis Hbounds
  /-- Identification: the limit satisfies a chosen solution concept. -/
  Hid : IdentificationHypothesis Hconv

/-!
## Top-level theorem (2D)
-/

/-- RS → (abstract) global regularity in 2D, via the composed bridge pipeline.

At this stage, “regularity” is represented by the existence of a limit Fourier trajectory
`u : ℝ → FourierState2D` together with the packaged identification property.
-/
theorem rs_implies_global_regularity_2d
    (H : RSNS2DPipelineHypothesis) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2,
        Filter.Tendsto (fun N : ℕ => (extendByZero (H.Hbounds.uN N t)) k) Filter.atTop
          (nhds ((u t) k)))
        ∧ H.Hid.IsSolution u
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.Hbounds.B) := by
  -- The result is exactly the continuum limit theorem from M5.
  simpa using (continuum_limit_exists H.Hbounds H.Hconv H.Hid)

/-- Variant of the top-level theorem where the “identification” is the **proved** coefficient bound:
we do not need a separate `IdentificationHypothesis` argument for this minimal `IsSolution` notion. -/
theorem rs_implies_global_regularity_2d_coeffBound
    (Hbounds : UniformBoundsHypothesis)
    (Hconv : ConvergenceHypothesis Hbounds) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2,
        Filter.Tendsto (fun N : ℕ => (extendByZero (Hbounds.uN N t)) k) Filter.atTop
          (nhds ((u t) k)))
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ Hbounds.B) := by
  -- Take the limit object from convergence, and use the derived bound lemma.
  refine ⟨Hconv.u, ?_, ?_⟩
  · simpa using Hconv.converges
  · intro t ht k
    simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := Hconv) t ht k)

/-- Variant of the top-level theorem where the derived “identification” is:

- the **proved** coefficient bound (from uniform bounds + convergence), and
- the **proved** divergence-free constraint (passed to the limit under modewise convergence),
  assuming each approximant is divergence-free in Fourier variables.

This avoids providing a separate `IdentificationHypothesis`. -/
theorem rs_implies_global_regularity_2d_divFreeCoeffBound
    (Hbounds : UniformBoundsHypothesis)
    (Hconv : ConvergenceHypothesis Hbounds)
    (hDF : ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2,
      divConstraint k ((extendByZero (Hbounds.uN N t)) k) = 0) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2,
        Filter.Tendsto (fun N : ℕ => (extendByZero (Hbounds.uN N t)) k) Filter.atTop
          (nhds ((u t) k)))
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ Hbounds.B)
        ∧ IsDivergenceFreeTraj u := by
  refine ⟨Hconv.u, ?_, ?_, ?_⟩
  · simpa using Hconv.converges
  · intro t ht k
    simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := Hconv) t ht k)
  · exact ConvergenceHypothesis.divFree_of_forall (HC := Hconv) hDF

/-- Variant of the top-level theorem where the derived “identification” is:

- the **proved** coefficient bound (from uniform bounds + convergence), and
- the **proved** linear Stokes/heat mild identity (passed to the limit under modewise convergence),
  assuming each approximant satisfies the same identity modewise for `t ≥ 0`.

This avoids providing a separate `IdentificationHypothesis`. -/
theorem rs_implies_global_regularity_2d_stokesMildCoeffBound
    (Hbounds : UniformBoundsHypothesis)
    (Hconv : ConvergenceHypothesis Hbounds)
    (ν : ℝ)
    (hMild :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (Hbounds.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (Hbounds.uN N 0) k)) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2,
        Filter.Tendsto (fun N : ℕ => (extendByZero (Hbounds.uN N t)) k) Filter.atTop
          (nhds ((u t) k)))
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ Hbounds.B)
        ∧ IsStokesMildTraj ν u := by
  refine ⟨Hconv.u, ?_, ?_, ?_⟩
  · simpa using Hconv.converges
  · intro t ht k
    simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := Hconv) t ht k)
  · exact ConvergenceHypothesis.stokesMild_of_forall (HC := Hconv) (ν := ν) hMild

/-- Same as `rs_implies_global_regularity_2d_stokesMildCoeffBound`, but returns the **differential**
(within `t ≥ 0`) Stokes/heat equation per mode.

This is derived from the mild identity via `IsStokesMildTraj.stokesODE`. -/
theorem rs_implies_global_regularity_2d_stokesODECoeffBound
    (Hbounds : UniformBoundsHypothesis)
    (Hconv : ConvergenceHypothesis Hbounds)
    (ν : ℝ)
    (hMild :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (Hbounds.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (Hbounds.uN N 0) k)) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2,
        Filter.Tendsto (fun N : ℕ => (extendByZero (Hbounds.uN N t)) k) Filter.atTop
          (nhds ((u t) k)))
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ Hbounds.B)
        ∧ IsStokesODETraj ν u := by
  refine ⟨Hconv.u, ?_, ?_, ?_⟩
  · simpa using Hconv.converges
  · intro t ht k
    simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := Hconv) t ht k)
  ·
    have hm : IsStokesMildTraj ν Hconv.u :=
      ConvergenceHypothesis.stokesMild_of_forall (HC := Hconv) (ν := ν) hMild
    exact IsStokesMildTraj.stokesODE hm

/-- Variant of the top-level theorem returning a first nonlinear (Duhamel-style) remainder identity.

This uses `ConvergenceHypothesis.nsDuhamel_of_forall` to pass the identity to the limit,
assuming the approximants satisfy the identity with remainders `D_N` that converge modewise. -/
theorem rs_implies_global_regularity_2d_nsDuhamelCoeffBound
    (Hbounds : UniformBoundsHypothesis)
    (Hconv : ConvergenceHypothesis Hbounds)
    (ν : ℝ)
    (D_N : ℕ → ℝ → FourierState2D) (D : ℝ → FourierState2D)
    (hD : ∀ t : ℝ, ∀ k : Mode2,
      Filter.Tendsto (fun N : ℕ => (D_N N t) k) Filter.atTop (nhds ((D t) k)))
    (hId :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (Hbounds.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (Hbounds.uN N 0) k) + (D_N N t) k) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2,
        Filter.Tendsto (fun N : ℕ => (extendByZero (Hbounds.uN N t)) k) Filter.atTop
          (nhds ((u t) k)))
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ Hbounds.B)
        ∧ IsNSDuhamelTraj ν D u := by
  refine ⟨Hconv.u, ?_, ?_, ?_⟩
  · simpa using Hconv.converges
  · intro t ht k
    simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := Hconv) t ht k)
  ·
    -- Pass the Duhamel-style identity to the limit.
    exact ConvergenceHypothesis.nsDuhamel_of_forall (HC := Hconv) (ν := ν) (D_N := D_N) (D := D) hD hId

/-- Variant of the top-level theorem returning a first nonlinear (Duhamel-style) remainder identity,
where the remainder is produced from the **Galerkin nonlinearity** via the Duhamel kernel integral.

This removes the need to provide `D_N`, `D`, and the approximation identity explicitly; the only
missing analytic ingredient is the dominated-convergence hypothesis `hDC` for the kernel integrands. -/
theorem rs_implies_global_regularity_2d_nsDuhamelCoeffBound_galerkinKernel
    (Hbounds : UniformBoundsHypothesis)
    (Hconv : ConvergenceHypothesis Hbounds)
    (ν : ℝ)
    (Bop : (N : ℕ) → ConvectionOp N)
    (hu :
      ∀ N : ℕ, ∀ s : ℝ,
        HasDerivAt (Hbounds.uN N) (galerkinNSRHS (N := N) ν (Bop N) (Hbounds.uN N s)) s)
    (hint :
      ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2,
        IntervalIntegrable (fun s : ℝ =>
          (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero ((Bop N) (Hbounds.uN N s) (Hbounds.uN N s)) k))
          MeasureTheory.volume 0 t)
    (F : ℝ → FourierState2D)
    (hDC :
      ∀ t : ℝ, ∀ k : Mode2,
        DuhamelKernelDominatedConvergenceAt ν
          (fun N : ℕ => fun s : ℝ => extendByZero ((Bop N) (Hbounds.uN N s) (Hbounds.uN N s))) F t k) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2,
        Filter.Tendsto (fun N : ℕ => (extendByZero (Hbounds.uN N t)) k) Filter.atTop
          (nhds ((u t) k)))
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ Hbounds.B)
        ∧ IsNSDuhamelTraj ν (duhamelKernelIntegral ν F) u := by
  classical
  refine ⟨Hconv.u, ?_, ?_, ?_⟩
  · simpa using Hconv.converges
  · intro t ht k
    simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := Hconv) t ht k)
  ·
    -- Define the forcing family from the Galerkin nonlinearity.
    let F_N : ℕ → ℝ → FourierState2D :=
      fun N : ℕ => fun s : ℝ => extendByZero ((Bop N) (Hbounds.uN N s) (Hbounds.uN N s))
    -- Approximant identity: derived from the Galerkin kernel lemma.
    have hId :
        ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
          (extendByZero (Hbounds.uN N t) k) =
            (heatFactor ν t k) • (extendByZero (Hbounds.uN N 0) k)
              + (duhamelKernelIntegral ν (F_N N) t) k := by
      intro N t _ht k
      simpa [F_N] using
        (galerkin_duhamelKernel_identity (N := N) (ν := ν) (B := Bop N) (u := Hbounds.uN N) (k := k) (t := t)
          (hu := fun s => hu N s) (hint := hint N t k))
    -- Pass the identity to the limit using the kernel/DCT wrapper.
    have hDC' : ∀ t : ℝ, ∀ k : Mode2, DuhamelKernelDominatedConvergenceAt ν F_N F t k := by
      intro t k
      simpa [F_N] using hDC t k
    exact
      ConvergenceHypothesis.nsDuhamel_of_forall_kernelIntegral (HC := Hconv) (ν := ν)
        (F_N := F_N) (F := F) hDC' hId

/-- Same as `rs_implies_global_regularity_2d_nsDuhamelCoeffBound_galerkinKernel`, but assumes dominated
convergence only for the **forcing** (not the kernel integrand), plus `0 ≤ ν`. -/
theorem rs_implies_global_regularity_2d_nsDuhamelCoeffBound_galerkinKernel_of_forcing
    (Hbounds : UniformBoundsHypothesis)
    (Hconv : ConvergenceHypothesis Hbounds)
    (ν : ℝ) (hν : 0 ≤ ν)
    (Bop : (N : ℕ) → ConvectionOp N)
    (hu :
      ∀ N : ℕ, ∀ s : ℝ,
        HasDerivAt (Hbounds.uN N) (galerkinNSRHS (N := N) ν (Bop N) (Hbounds.uN N s)) s)
    (hint :
      ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2,
        IntervalIntegrable (fun s : ℝ =>
          (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero ((Bop N) (Hbounds.uN N s) (Hbounds.uN N s)) k))
          MeasureTheory.volume 0 t)
    (F : ℝ → FourierState2D)
    (hF :
      ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2,
        ForcingDominatedConvergenceAt
          (F_N := fun N : ℕ => fun s : ℝ => extendByZero ((Bop N) (Hbounds.uN N s) (Hbounds.uN N s)))
          (F := F) t k) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2,
        Filter.Tendsto (fun N : ℕ => (extendByZero (Hbounds.uN N t)) k) Filter.atTop
          (nhds ((u t) k)))
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ Hbounds.B)
        ∧ IsNSDuhamelTraj ν (duhamelKernelIntegral ν F) u := by
  classical
  refine ⟨Hconv.u, ?_, ?_, ?_⟩
  · simpa using Hconv.converges
  · intro t ht k
    simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := Hconv) t ht k)
  ·
    let F_N : ℕ → ℝ → FourierState2D :=
      fun N : ℕ => fun s : ℝ => extendByZero ((Bop N) (Hbounds.uN N s) (Hbounds.uN N s))
    have hId :
        ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
          (extendByZero (Hbounds.uN N t) k) =
            (heatFactor ν t k) • (extendByZero (Hbounds.uN N 0) k)
              + (duhamelKernelIntegral ν (F_N N) t) k := by
      intro N t _ht k
      simpa [F_N] using
        (galerkin_duhamelKernel_identity (N := N) (ν := ν) (B := Bop N) (u := Hbounds.uN N) (k := k) (t := t)
          (hu := fun s => hu N s) (hint := hint N t k))
    have hF' : ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2, ForcingDominatedConvergenceAt (F_N := F_N) (F := F) t k := by
      intro t ht k
      simpa [F_N] using hF t ht k
    exact
      ConvergenceHypothesis.nsDuhamel_of_forall_kernelIntegral_of_forcing (HC := Hconv) (ν := ν) hν
        (F_N := F_N) (F := F) hF' hId

/-- Same as `rs_implies_global_regularity_2d_nsDuhamelCoeffBound_galerkinKernel_of_forcing`, but
takes the more concrete `GalerkinForcingDominatedConvergenceHypothesis` for the Galerkin forcing. -/
theorem rs_implies_global_regularity_2d_nsDuhamelCoeffBound_galerkinKernel_of_forcingHyp
    (Hbounds : UniformBoundsHypothesis)
    (Hconv : ConvergenceHypothesis Hbounds)
    (ν : ℝ) (hν : 0 ≤ ν)
    (Bop : (N : ℕ) → ConvectionOp N)
    (hu :
      ∀ N : ℕ, ∀ s : ℝ,
        HasDerivAt (Hbounds.uN N) (galerkinNSRHS (N := N) ν (Bop N) (Hbounds.uN N s)) s)
    (hint :
      ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2,
        IntervalIntegrable (fun s : ℝ =>
          (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero ((Bop N) (Hbounds.uN N s) (Hbounds.uN N s)) k))
          MeasureTheory.volume 0 t)
    (hForce : GalerkinForcingDominatedConvergenceHypothesis Hbounds Bop) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2,
        Filter.Tendsto (fun N : ℕ => (extendByZero (Hbounds.uN N t)) k) Filter.atTop
          (nhds ((u t) k)))
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ Hbounds.B)
        ∧ IsNSDuhamelTraj ν (duhamelKernelIntegral ν hForce.F) u := by
  refine
    rs_implies_global_regularity_2d_nsDuhamelCoeffBound_galerkinKernel_of_forcing
      (Hbounds := Hbounds) (Hconv := Hconv) (ν := ν) hν (Bop := Bop) (hu := hu) (hint := hint)
      (F := hForce.F) ?_
  intro t ht k
  simpa [galerkinForcing] using (GalerkinForcingDominatedConvergenceHypothesis.forcingDCTAt (hF := hForce) t ht k)

end Regularity2D

end IndisputableMonolith.ClassicalBridge.Fluids
