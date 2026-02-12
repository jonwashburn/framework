import Hodge.GMT.Current
import Hodge.Analytic.Currents
import Hodge.Analytic.Integration.HausdorffMeasure
import Hodge.Analytic.Integration.StokesTheorem

/-!
# GMT: Integration Currents

This module provides the **integration current** infrastructure connecting the GMT layer
to the real integration machinery in `Hodge.Analytic.Currents`.

## Round 10 Update (M4: Currents Bridge)

The integration current is now **properly wired** to the `Hodge.Analytic.Currents`
infrastructure:

- `integrationCurrentReal_data` uses `ClosedSubmanifoldData.toIntegrationData`,
  which connects a concrete `ClosedSubmanifoldData` to `IntegrationData → Current`.
- The underlying integration uses Hausdorff integration on oriented rectifiable data.
- Linearity, boundedness, and Stokes bounds are proven (not axiomatized)

## Mathematical Content

For a closed (compact, boundaryless) submanifold Z ⊂ X of complex dimension p:

  `[Z](ω) = ∫_Z ω`

where the integral is with respect to the 2p-dimensional Hausdorff measure.

## Key Definitions

- `integrationCurrentReal_data`: the data‑first integration current constructor
- `integrationCurrent_data`: codimension‑parameterized data‑first constructor
- `integrationCurrentReal` / `integrationCurrent`: legacy wrappers (compatibility only; do not use on proof track)

## Connection to Cohomology

The integration current `[Z]` induces a cohomology class via:
1. `[Z]` acts on closed forms by integration
2. This action descends to cohomology (by Stokes: `[Z](dω) = ∫_∂Z ω = 0` for closed Z)
3. The cohomology class is the Poincaré dual of Z

See `Hodge.GMT.PoincareDuality` for the full construction.

## References

- [H. Federer, "Geometric Measure Theory", 1969, §4.1.7]
- [Griffiths-Harris, "Principles of Algebraic Geometry", 1978, Ch. 0]
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

namespace Hodge.GMT

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-! ## Integration Current (Real Implementation)

The following definitions wire to the actual integration infrastructure in
`Hodge.Analytic.Currents`, which uses `ClosedSubmanifoldData` /
`OrientedRectifiableSetData` and `hausdorffIntegrate`. -/

/-- **Real Integration Current** (explicit data).

    This is the data-first constructor: no typeclass binders, just a
    concrete `ClosedSubmanifoldData` object. -/
noncomputable def integrationCurrentReal_data (k : ℕ)
    (data : ClosedSubmanifoldData n X k) : DeRhamCurrent n X k :=
  data.toIntegrationData.toCurrent

/-- **Real Integration Current** (compatibility-only wrapper; prefer `*_data`).

    For a set `Z` with Stokes data, this produces a `Current` that genuinely
    integrates forms over `Z` using the Hausdorff measure infrastructure.

    **Proof-track guidance**: do not use this in new lemmas; pass `ClosedSubmanifoldData` directly. -/
noncomputable def integrationCurrentReal (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X k Z] : DeRhamCurrent n X k :=
  integrationCurrentReal_data (n := n) (X := X) k
    (ClosedSubmanifoldStokesData.data (n := n) (X := X) (k := k) (Z := Z))

/-- Integration current in degree `k` (explicit data). -/
noncomputable def integrationCurrentK_data (k : ℕ)
    (data : ClosedSubmanifoldData n X k) : DeRhamCurrent n X k :=
  integrationCurrentReal_data (n := n) (X := X) k data

/-- Integration current in degree `k` over a set `Z` (compatibility-only wrapper; prefer `*_data`). -/
noncomputable def integrationCurrentK (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X k Z] : DeRhamCurrent n X k :=
  integrationCurrentReal (n := n) (X := X) k Z

/-- Integration current with Stokes data (compatibility-only wrapper; prefer `*_data`). -/
noncomputable def integrationCurrentWithStokes (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X k Z] : DeRhamCurrent n X k :=
  integrationCurrentReal (n := n) (X := X) k Z

/-- Integration current for a codimension parameter `p`, returning degree `2*p`.

    **Note**: Complex submanifolds of complex dimension p have real dimension 2p,
    so the integration current lives in degree 2p (as a k-current for k = 2p forms).

This matches the signature used in `docs/OPERATIONAL_PLAN_5_AGENTS.md`. -/
noncomputable def integrationCurrent_data (p : ℕ)
    (data : ClosedSubmanifoldData n X (2 * p)) : DeRhamCurrent n X (2 * p) :=
  integrationCurrentK_data (n := n) (X := X) (k := 2 * p) data

/-- Integration current for a codimension parameter `p`
    (compatibility-only wrapper; prefer `*_data`). -/
noncomputable def integrationCurrent (p : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X (2 * p) Z] : DeRhamCurrent n X (2 * p) :=
  integrationCurrentK (n := n) (X := X) (k := 2 * p) Z

/-- Linearity of the integration current evaluation (degree-`k` form). -/
theorem integrationCurrentK_linear_data (k : ℕ) (c : ℝ)
    (data : ClosedSubmanifoldData n X k) (ω₁ ω₂ : SmoothForm n X k) :
    (integrationCurrentK_data (n := n) (X := X) k data).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrentK_data (n := n) (X := X) k data).toFun ω₁ +
        (integrationCurrentK_data (n := n) (X := X) k data).toFun ω₂ := by
  simpa [DeRhamCurrent] using
    (Hodge.GMT.current_eval_linear (T := integrationCurrentK_data (n := n) (X := X) k data) c ω₁ ω₂)

/-- Linearity of the integration current evaluation (degree-`k` form, wrapper).

Compatibility-only: prefer `integrationCurrentK_linear_data` with explicit
`ClosedSubmanifoldData`. -/
theorem integrationCurrentK_linear (k : ℕ) (Z : Set X) (c : ℝ)
    [ClosedSubmanifoldStokesData n X k Z]
    (ω₁ ω₂ : SmoothForm n X k) :
    (integrationCurrentK (n := n) (X := X) k Z).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrentK (n := n) (X := X) k Z).toFun ω₁ +
        (integrationCurrentK (n := n) (X := X) k Z).toFun ω₂ := by
  simpa using
    (integrationCurrentK_linear_data (n := n) (X := X) (k := k) (c := c)
      (data := ClosedSubmanifoldStokesData.data (n := n) (X := X) (k := k) (Z := Z)) ω₁ ω₂)

/-- Linearity of the integration current evaluation (codimension form, degree `2*p`). -/
theorem integrationCurrent_linear_data (p : ℕ) (c : ℝ)
    (data : ClosedSubmanifoldData n X (2 * p))
    (ω₁ ω₂ : SmoothForm n X (2 * p)) :
    (integrationCurrent_data (n := n) (X := X) p data).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrent_data (n := n) (X := X) p data).toFun ω₁ +
        (integrationCurrent_data (n := n) (X := X) p data).toFun ω₂ := by
  simpa [DeRhamCurrent] using
    (Hodge.GMT.current_eval_linear (T := integrationCurrent_data (n := n) (X := X) p data) c ω₁ ω₂)

/-- Linearity of the integration current evaluation (wrapper).

Compatibility-only: prefer `integrationCurrent_linear_data`. -/
theorem integrationCurrent_linear (p : ℕ) (Z : Set X) (c : ℝ)
    [ClosedSubmanifoldStokesData n X (2 * p) Z]
    (ω₁ ω₂ : SmoothForm n X (2 * p)) :
    (integrationCurrent (n := n) (X := X) p Z).toFun (c • ω₁ + ω₂) =
      c * (integrationCurrent (n := n) (X := X) p Z).toFun ω₁ +
        (integrationCurrent (n := n) (X := X) p Z).toFun ω₂ := by
  simpa using
    (integrationCurrent_linear_data (n := n) (X := X) (p := p) (c := c)
      (data := ClosedSubmanifoldStokesData.data (n := n) (X := X) (k := 2 * p) (Z := Z)) ω₁ ω₂)

/-! ## Integration Current Properties (with Stokes data) -/

/-- The real integration current uses `ClosedSubmanifoldStokesData.toIntegrationData`. -/
theorem integrationCurrentReal_data_toFun_eq (k : ℕ)
    (data : ClosedSubmanifoldData n X k) (ω : SmoothForm n X k) :
    (integrationCurrentReal_data (n := n) (X := X) k data).toFun ω =
      data.toIntegrationData.integrate ω := by
  rfl

/- Compatibility-only: prefer `integrationCurrentReal_data_toFun_eq`. -/
theorem integrationCurrentReal_toFun_eq (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X k Z] (ω : SmoothForm n X k) :
    (integrationCurrentReal (n := n) (X := X) k Z).toFun ω =
      (ClosedSubmanifoldStokesData.toIntegrationData (n := n) (X := X) (k := k) (Z := Z)).integrate ω := by
  rfl

/-! ## Connection to Cohomology

The integration current defines a linear functional on forms that descends to cohomology.
This is the foundation for the cycle class map `Z ↦ [Z]`. -/

/-- **Integration induces cohomology pairing** (conceptual statement).

    For a closed submanifold Z and a closed form ω:
    - `[Z](ω)` depends only on the cohomology class of ω
    - This defines a map `H^k(X) → ℝ`, which by Poincaré duality corresponds to
      an element of `H^{2n-k}(X)`

    **Mathematical Content** (Stokes theorem):
    If ω = dη, then `[Z](ω) = [Z](dη) = ∫_Z dη = ∫_∂Z η = 0` (since ∂Z = ∅).
    Therefore `[Z]` descends to a well-defined functional on cohomology. -/
theorem integration_descends_to_cohomology_data (k : ℕ)
    (data : ClosedSubmanifoldData n X (k + 1)) (η : SmoothForm n X k) :
    (integrationCurrentReal_data (n := n) (X := X) (k + 1) data).toFun (smoothExtDeriv η) = 0 := by
  -- Use the data-first Stokes lemma specialized to closed submanifold data.
  simpa [integrationCurrentReal_data_toFun_eq] using
    (StokesTheorem.closedSubmanifold_integral_extDeriv_eq_zero (n := n) (X := X)
      (data := data) (ω := η))

/-- Compatibility-only wrapper: prefer `integration_descends_to_cohomology_data`. -/
theorem integration_descends_to_cohomology (k : ℕ) (Z : Set X)
    [ClosedSubmanifoldStokesData n X (k + 1) Z]
    (η : SmoothForm n X k) :
    (integrationCurrentReal (n := n) (X := X) (k + 1) Z).toFun (smoothExtDeriv η) = 0 := by
  simpa using
    (integration_descends_to_cohomology_data (n := n) (X := X) (k := k)
      (data := ClosedSubmanifoldStokesData.data (n := n) (X := X) (k := k + 1) (Z := Z)) η)

end Hodge.GMT
