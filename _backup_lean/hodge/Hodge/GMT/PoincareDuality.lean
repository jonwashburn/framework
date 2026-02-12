import Hodge.Classical.CycleClass
import Hodge.Classical.PoincareDualityFromCurrents
import Hodge.GMT.CurrentToForm
import Hodge.GMT.IntegrationCurrent

/-!
# GMT: Poincaré Duality Interface

This module provides the **Poincaré duality bridge** connecting:
1. Geometric objects (algebraic subvarieties Z)
2. Currents (the integration current `[Z]`)
3. Differential forms (the Poincaré dual form `η_Z`)
4. Cohomology classes (the cycle class `[Z] ∈ H^{2p}(X)`)

## Round 10 Update (M4: Currents Bridge)

The Poincaré duality interface now documents the **full mathematical pipeline**:

```
  Z (subvariety) ─────────────────────────────────────────────────┐
       │                                                           │
       ▼                                                           │
  [Z] (integration current via Hausdorff measure)                  │
       │                                                           │
       ▼                                                           │
  η_Z (Poincaré dual form: closed 2p-form)                         │
       │                                                           │
       ▼                                                           │
  [η_Z] ∈ H^{2p}(X) (cohomology class)  ◄──────────────────────────┘
```

## Current Implementation Status

1. **Integration current** (`Hodge.GMT.IntegrationCurrent`): ✅ Connected to real
   Hausdorff integration infrastructure via `ClosedSubmanifoldData` →
   `IntegrationData` → `Current`

2. **Poincaré dual form** (`Hodge.Classical.CycleClass`): ⚠️ Deep interface
   `PoincareDualityFromCurrentsData` (no universal instance). The mathematical pipeline is
   documented but the actual form construction requires the current→form regularization.

3. **Cohomology class**: ✅ Correctly constructed from the PD form using `ofForm`

## Mathematical Background

**Poincaré Duality** (de Rham, 1931): On a compact oriented n-manifold X, there is
an isomorphism `PD : H_k(X) → H^{n-k}(X)` given by:

  `⟨PD([Z]), [α]⟩ = ∫_Z α`

where `[Z] ∈ H_k(X)` is a homology class represented by a k-cycle Z, and
`[α] ∈ H^k(X)` is a cohomology class represented by a closed k-form α.

The Poincaré dual form `η_Z` is characterized by:

  `∫_X η_Z ∧ α = ∫_Z α` for all closed (2n-2p)-forms α

## References

- [de Rham, "Variétés Différentiables", 1955]
- [Bott-Tu, "Differential Forms in Algebraic Topology", GTM 82, 1982]
- [Griffiths-Harris, "Principles of Algebraic Geometry", 1978, Ch. 0-1]
- [Federer, "Geometric Measure Theory", 1969, §4.1]
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

namespace Hodge.GMT

/-! ## Re-exports from CycleClass

These aliases provide the module/name layout referenced by the operational plan. -/

abbrev PoincareDualFormData := CycleClass.PoincareDualFormData

abbrev poincareDualFormExists := CycleClass.poincareDualFormExists
abbrev poincareDualForm := CycleClass.poincareDualForm

/-- Construct the Poincaré dual form via the `CycleClass` interface.

This is the *current* bridge used by the proof-track development.

**Status**: Requires an explicit `PoincareDualityFromCurrentsData` instance (no universal placeholder).
See `Hodge.Classical.CycleClass` for the interface. -/
-- Compatibility-only: this uses the legacy set-based PD interface.
abbrev poincareDualForm_construct_cycleClass := CycleClass.poincareDualForm

/-- Poincaré dual form constructed from the (integration current) → (regularization) pipeline.

This matches the operational plan sketch:
`regularizeCurrentToForm (integrationCurrent_data p data)`.

**Round 10 Note**: The integration current is now real (via Hausdorff measure), and
`regularizeCurrentToForm` is exposed as an explicit regularization interface.
When regularization is implemented, this will produce the actual Poincaré dual form. -/
noncomputable def poincareDualForm_construct_fromCurrentData {n : ℕ} {X : Type*} {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [CurrentRegularizationData n X (2 * p)]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    SmoothForm n X (2 * p) :=
  regularizeCurrentToForm (n := n) (X := X) (k := 2 * p)
    (integrationCurrent_data (n := n) (X := X) p data)

/-- Same constructor, but using a `ClosedSubmanifoldStokesData` instance for a carrier set.

Compatibility-only: prefer `poincareDualForm_construct_fromCurrentData` with explicit data. -/
noncomputable def poincareDualForm_construct_fromCurrent {n : ℕ} {X : Type*} {p : ℕ}
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [CurrentRegularizationData n X (2 * p)]
    (Z : Set X) [ClosedSubmanifoldStokesData n X (2 * p) Z] :
    SmoothForm n X (2 * p) :=
  poincareDualForm_construct_fromCurrentData (n := n) (X := X) (p := p)
    (data := ClosedSubmanifoldStokesData.data (n := n) (X := X) (k := 2 * p) (Z := Z))

/-- Construct the Poincaré dual form via the "current → regularize" pipeline.

This matches the operational plan naming (`poincareDualForm_construct`). -/
noncomputable abbrev poincareDualForm_construct := @poincareDualForm_construct_fromCurrentData

/-! ## Connection to cohomology

This section documents how the integration current induces a cohomology class
and how this relates to the Poincaré dual form. -/

universe u

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

/-- A cohomology class associated to a set `Z`, using the *current* set-based PD-form interface.

This uses the `CycleClass.poincareDualForm` interface (which provides closedness), so it
produces a well-typed de Rham class.

**Mathematical Content**: This is the cycle class `[Z] ∈ H^{2p}(X, ℝ)`.

**Implementation**: Uses `ofForm` with the PD form and its closedness proof.

Compatibility-only: proof track uses `gmt_cycle_to_cohomology_path_data`. -/
-- Compatibility wrapper: prefer `gmt_cycle_to_cohomology_path_data` with
-- explicit `ClosedSubmanifoldData` when available.
noncomputable def gmt_cycle_to_cohomology_path (p : ℕ) [CycleClass.PoincareDualFormExists n X p] (Z : Set X) :
    DeRhamCohomologyClass n X (2 * p) :=
  Hodge.ofForm (CycleClass.poincareDualForm n X p Z) (CycleClass.poincareDualForm_isClosed n X p Z)

/-- Data-first cohomology class associated to explicit `ClosedSubmanifoldData`. -/
noncomputable def gmt_cycle_to_cohomology_path_data (p : ℕ)
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    DeRhamCohomologyClass n X (2 * p) :=
  Hodge.ofForm (CycleClass.poincareDualForm_data n X p data)
    (CycleClass.poincareDualForm_data_isClosed_ofCurrents n X p data)

/-- The cycle class of the empty set is the zero cohomology class.

Compatibility-only: proof track uses `gmt_cycle_to_cohomology_empty_data`. -/
theorem gmt_cycle_to_cohomology_empty (p : ℕ) [CycleClass.PoincareDualFormExists n X p] :
    gmt_cycle_to_cohomology_path (n := n) (X := X) p ∅ =
      Hodge.ofForm 0 (isFormClosed_zero (n := n) (X := X) (k := 2 * p)) := by
  unfold gmt_cycle_to_cohomology_path
  congr 1
  exact CycleClass.poincareDualForm_empty n X p

/-! ### Data-first empty-set compatibility -/

theorem gmt_cycle_to_cohomology_empty_data (p : ℕ)
    [CycleClass.PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) (h : data.carrier = ∅) :
    gmt_cycle_to_cohomology_path_data (n := n) (X := X) p data =
      Hodge.ofForm 0 (isFormClosed_zero (n := n) (X := X) (k := 2 * p)) := by
  unfold gmt_cycle_to_cohomology_path_data
  -- Reduce to the empty-carrier property from the data-first PD form interface.
  congr 1
  exact CycleClass.poincareDualForm_data_empty_ofCurrents n X p data h

/-! ## The Full Poincaré Duality Pipeline (Documentation)

The following section documents the full mathematical pipeline from subvarieties to
cohomology classes. This is the "M4 bridge" that connects:

1. **Subvarieties** (algebraic objects)
2. **Integration currents** (analytic objects via Hausdorff measure)
3. **Poincaré dual forms** (differential forms)
4. **Cohomology classes** (topological invariants)

### Current Status

| Step | Status | Implementation |
|------|--------|---------------|
| Z → [Z] (current) | ✅ Real | `integrationCurrent_data` via `ClosedSubmanifoldData` / `hausdorffIntegrate` |
| [Z] → η_Z (form) | ⚠️ Interface | `regularizeCurrentToForm` (explicit data, no stub) |
| η_Z → [η_Z] (class) | ✅ Real | `ofForm` with closedness proof |
| Direct: Z → [Z] | ✅ Placeholder | `poincareDualForm` (Kähler powers) |

### Mathematical Validation

The data-first bridge now defines `poincareDualForm_data` **explicitly** as
regularization of the integration current. Closedness/empty-carrier properties
are tracked via `PoincareDualityFromCurrentsData` (which yields
`PoincareDualFormFromCurrentData`). The set-based interface
`PoincareDualFormExists` remains a compatibility layer for legacy call sites.

This keeps the proof track honest while the regularization machinery is under
development.

### Gap Analysis (for future work)

To complete the "current → form" bridge, one needs:

1. **Smoothing operators**: Mollification of distributions on manifolds
2. **Hodge theory**: The unique harmonic representative in a cohomology class
3. **Current regularization**: T ↦ T_ε where T_ε is smooth and [T_ε] = [T]

These are substantial analytic results that require:
- Elliptic theory for the Laplacian
- Sobolev embedding theorems on manifolds
- Careful treatment of non-compact supports

Reference: [de Rham, "Variétés Différentiables", 1955, Ch. V]
Reference: [Hodge, "The Theory and Applications of Harmonic Integrals", 1941]
-/

/-!
**Cycle class is well-defined** (conceptual statement).

The cohomology class `[Z] ∈ H^{2p}(X)` depends only on the homology class of Z.

Mathematical content: If Z₁ and Z₂ are homologous cycles (Z₁ - Z₂ = ∂W),
then their cycle classes agree: `[Z₁] = [Z₂]`.

Proof sketch: By Stokes, for any closed form α:
`∫_{Z₁} α - ∫_{Z₂} α = ∫_{∂W} α = ∫_W dα = 0`.

This is currently kept as documentation (no semantic stub theorem). -/

/-!
**Poincaré duality pairing** (conceptual statement).

For Z a p-codimensional cycle and α a closed (2n-2p)-form:
`⟨[Z], [α]⟩ = ∫_Z α`.

This is the defining characterization of the Poincaré dual form.
Currently kept as documentation (no semantic stub theorem). -/

end Hodge.GMT
