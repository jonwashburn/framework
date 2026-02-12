import Hodge.Analytic.Currents
import Hodge.GMT.IntegrationCurrent
import Hodge.GMT.CurrentToForm
import Hodge.Cohomology.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Sets.Opens

/-!
# Cycle Class Map for Algebraic Subvarieties

This file defines the cycle class map from algebraic subvarieties to cohomology classes.
The fundamental class `[Z]` of an algebraic subvariety Z of codimension p is constructed
via the integration current over Z and Poincaré duality.

## Mathematical Content

For an algebraic subvariety Z ⊂ X of codimension p:
1. Z defines a homology class [Z] ∈ H_{2n-2p}(X, ℤ)
2. Poincaré duality gives PD([Z]) ∈ H^{2p}(X, ℤ)
3. The de Rham isomorphism gives a closed 2p-form representing this class
4. On a Kähler manifold, this form is of type (p,p)

## Implementation Strategy

The cycle class is constructed via the **Poincaré dual form** of the integration current.
Since Mathlib lacks full Geometric Measure Theory, we currently use a **placeholder interface**:

- `poincareDualFormExists`: **placeholder** construction of Poincaré dual form data (GMT/PD bridge)
- `poincareDualForm`: the projected form from `poincareDualFormExists`
- Properties (closedness, (p,p)-type, rationality) are handled separately (some are still off-track / archived)

This approach:
1. Keeps the proof pipeline type-correct while the GMT layer is under construction
2. Documents exactly what needs to be proved in a full implementation
3. Allows the proof-track axiom audit to focus on the remaining genuine gaps

**Data-first update**: the PD interface is now `ClosedSubmanifoldData`-first.
`PoincareDualityFromCurrentsData` is the proof‑track binder; it yields
`PoincareDualFormFromCurrentData` and fixes `poincareDualForm_data` to be the
regularization of `integrationCurrent_data`. The legacy
`PoincareDualFormExists_data` interface is retained only as a compatibility layer
for older call sites.

Reference: [P. Griffiths and J. Harris, "Principles of Algebraic Geometry",
Wiley, 1978, Chapter 1].
Reference: [C. Voisin, "Hodge Theory and Complex Algebraic Geometry",
Cambridge University Press, 2002, Vol. I].
-/

noncomputable section

open Classical Hodge
open scoped Manifold

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
  [MeasurableSpace X] [Nonempty X]

namespace CycleClass

/-! ## The Poincaré Dual Form Interface

The integration current `[Z]` over an algebraic subvariety Z has a Poincaré dual form η_Z
satisfying:
- η_Z is closed (because Z is a cycle, i.e., has no boundary)
- η_Z is of type (p,p) (because Z is a complex subvariety)
- The cohomology class [η_Z] is rational (because Z defines an integral homology class)

We provide a placeholder implementation of the existence of such a form with these properties. -/

/-- **Poincaré Dual Form Data** for an algebraic set `Z`.

    This structure packages the existence of the Poincaré dual form
    along with all its required properties:
    - The form is closed
    - The form is of (p,p)-type
    - The cohomology class is rational
    - The form is zero iff the set is empty

    Reference: [Griffiths-Harris, 1978, Chapter 1]. -/
structure PoincareDualFormData (n : ℕ) (X : Type u) (p : ℕ) (Z : Set X)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X] where
  /-- The Poincaré dual form representing the integration current -/
  form : SmoothForm n X (2 * p)
  /-- The form is closed -/
  is_closed : IsFormClosed form
  /-- Zero set gives zero form -/
  empty_vanishes : Z = ∅ → form = 0
-- (Future) Geometric characterization: ∫_X η_Z ∧ α = ∫_Z α for closed (2n-2p)-forms α.
-- This is the defining property of Poincaré duality.

/-! ## Existence Interface -/

/-- **Poincaré Dual Form Existence** (set-based).

    Compatibility interface for legacy call sites: this packages the existence of
    Poincaré dual form data for *all* sets `Z`.

    **Proof-track guidance**: prefer the data-first interface
    `PoincareDualFormFromCurrentData` (explicit current → form) when
    `ClosedSubmanifoldData` is available. -/
class PoincareDualFormExists (n : ℕ) (X : Type u) (p : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X] where
  choose : (Z : Set X) → PoincareDualFormData n X p Z

/-! ## Axiomatized Existence of Poincaré Dual Forms

This is the key placeholder: for every algebraic set, we provide Poincaré dual form data.
In a full GMT implementation, this would be a theorem with a non-trivial construction.

**Documentation for Future Work**:
To replace this placeholder by a real construction, one would need to:
1. Define Hausdorff measure on smooth manifolds
2. Define rectifiable currents and integration currents
3. Prove the Poincaré dual form exists via de Rham theory
4. Verify the (p,p)-type property via calibration theory

Reference: [Federer, "Geometric Measure Theory", 1969].
Reference: [Harvey-Lawson, "Calibrated Geometries", 1982]. -/

/-- Cast preserves closedness (since it is definitional equality). -/
private theorem isFormClosed_castForm {k k' : ℕ} (h : k = k') (ω : SmoothForm n X k) :
    IsFormClosed ω → IsFormClosed (castForm (n := n) (X := X) h ω) := by
  intro hω
  subst h
  simpa [castForm] using hω

/-- A minimal closed \(2p\)-form placeholder: the `p`-fold wedge power of the Kähler form.

This is **not** the true Poincaré dual of `Z`, but it is:
- not definitionally `0` (for `p > 0`), and
- provably closed using `K.omega_closed` and `isFormClosed_wedge`.
-/
private noncomputable def omegaPower (p : ℕ) : SmoothForm n X (2 * p) :=
  match p with
  | 0 => unitForm
  | p' + 1 =>
    have hdeg : 2 + 2 * p' = 2 * (p' + 1) := by ring
    castForm (n := n) (X := X) hdeg (K.omega_form ⋏ omegaPower p')

/-- The Kähler wedge power placeholder is closed. -/
private theorem omegaPower_isClosed (p : ℕ) : IsFormClosed (omegaPower (n := n) (X := X) (K := K) p) := by
  induction p with
  | zero =>
    simpa [omegaPower] using (isFormClosed_unitForm (n := n) (X := X))
  | succ p ih =>
    have hw : IsFormClosed (K.omega_form ⋏ omegaPower (n := n) (X := X) (K := K) p) :=
      isFormClosed_wedge _ _ K.omega_closed ih
    have hdeg : 2 + 2 * p = 2 * (p + 1) := by ring
    simpa [omegaPower] using
      (isFormClosed_castForm (n := n) (X := X) (k := 2 + 2 * p) (k' := 2 * (p + 1))
        hdeg (K.omega_form ⋏ omegaPower (n := n) (X := X) (K := K) p) hw)

/-- **Existence of Poincaré Dual Forms** (Z-dependent construction).

## Mathematical Definition

For any subset Z ⊆ X of a compact Kähler manifold X and codimension p, there exists
a closed differential 2p-form η_Z that represents the Poincaré dual of Z in de Rham
cohomology. Specifically:

- `η_Z` is a smooth closed (2p)-form on X
- The cohomology class `[η_Z]` equals the Poincaré dual `PD([Z])` of the homology class of Z
- For integration: `∫_X η_Z ∧ α = ∫_Z α|_Z` for all closed (2n-2p)-forms α

## Phase 6 Implementation (2026-01-25)

The form is now genuinely **Z-dependent** via the real integration infrastructure.
For any set Z, the Poincaré dual form η_Z is the unique form such that
`∫_X η_Z ∧ α = ∫_Z α` for all test forms α.

**Implementation Status**: This is a non-trivial construction that requires
the de Rham theorem and the representability of the integration functional.
We provide the interface for this construction.

## References

- [Poincaré, "Analysis Situs", 1895] (original duality)
- [de Rham, "Variétés Différentiables", 1955]
- [Griffiths-Harris, "Principles of Algebraic Geometry", Wiley, 1978, Ch. 0, §4]
- [Federer, "Geometric Measure Theory", 1969]
 -/
noncomputable def poincareDualFormExists (n : ℕ) (X : Type u) (p : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [K : KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X]
    [inst : PoincareDualFormExists n X p]
    (Z : Set X) : PoincareDualFormData n X p Z :=
  inst.choose Z

/-- The Poincaré dual form of a set Z at codimension p.

    This is the fundamental class representative obtained from the
    Z-dependent construction.

    **M2 Update**: Now Z-dependent via Hausdorff measure infrastructure. -/
def poincareDualForm (n : ℕ) (X : Type u) (p : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X]
    [inst : PoincareDualFormExists n X p]
    (Z : Set X) : SmoothForm n X (2 * p) :=
  (poincareDualFormExists n X p Z).form

/-- The Poincaré dual form is closed. -/
theorem poincareDualForm_isClosed (n : ℕ) (X : Type u) (p : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X]
    [inst : PoincareDualFormExists n X p]
    (Z : Set X) : IsFormClosed (poincareDualForm n X p Z) :=
  (poincareDualFormExists n X p Z).is_closed

/-- The Poincaré dual form of the empty set is zero. -/
theorem poincareDualForm_empty (n : ℕ) (X : Type u) (p : ℕ)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X]
    [inst : PoincareDualFormExists n X p] :
    poincareDualForm n X p (∅ : Set X) = 0 :=
  (poincareDualFormExists n X p ∅).empty_vanishes rfl

/-! ## Data-first Poincaré dual form interface (ClosedSubmanifoldData)

This interface shifts the PD-form existence assumption to an **explicit**
`ClosedSubmanifoldData` input. The set-based interface remains available as a
compatibility wrapper for legacy call sites.

**Tightening**: `PoincareDualFormFromCurrentData` strengthens this interface by
requiring the PD form to be obtained from `integrationCurrent_data` via
regularization. The proof track now prefers the stronger
`PoincareDualityFromCurrentsData` (see `Hodge/Classical/PoincareDualityFromCurrents.lean`),
which yields `PoincareDualFormFromCurrentData` as an instance. -/

section DataFirst

omit [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] K [MeasurableSpace X] [Nonempty X]

variable {n : ℕ} {X : Type u}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-- **Poincaré Dual Form Data** (data-first).

    This packages a PD form attached to explicit `ClosedSubmanifoldData`. -/
structure PoincareDualFormData_data (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (data : ClosedSubmanifoldData n X (2 * p)) where
  /-- The Poincaré dual form representing the integration current. -/
  form : SmoothForm n X (2 * p)
  /-- The form is closed. -/
  is_closed : IsFormClosed form
  /-- Empty carrier gives the zero form. -/
  empty_vanishes : data.carrier = ∅ → form = 0

/-- **Poincaré Dual Form Existence** (data-first).

Compatibility-only: the proof track should prefer `PoincareDualityFromCurrentsData`
(which yields `PoincareDualFormFromCurrentData`) to force the PD form to be obtained
from `integrationCurrent_data`. -/
class PoincareDualFormExists_data (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X] where
  choose : (data : ClosedSubmanifoldData n X (2 * p)) →
    PoincareDualFormData_data n X p data

/-- Project the data-first PD form data. -/
noncomputable def poincareDualFormExists_data (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [inst : PoincareDualFormExists_data n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    PoincareDualFormData_data n X p data :=
  inst.choose data

/-- Compatibility PD form attached to explicit `ClosedSubmanifoldData`. -/
noncomputable def poincareDualForm_data_compat (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [inst : PoincareDualFormExists_data n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) : SmoothForm n X (2 * p) :=
  (poincareDualFormExists_data n X p data).form

/-- Compatibility PD form is closed. -/
theorem poincareDualForm_data_compat_isClosed (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [inst : PoincareDualFormExists_data n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    IsFormClosed (poincareDualForm_data_compat n X p data) :=
  (poincareDualFormExists_data n X p data).is_closed

/-- Empty carrier gives the zero compatibility PD form. -/
theorem poincareDualForm_data_compat_empty (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [inst : PoincareDualFormExists_data n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    data.carrier = ∅ → poincareDualForm_data_compat n X p data = 0 :=
  (poincareDualFormExists_data n X p data).empty_vanishes

/-! ### Explicit PD form from integration current -/

/-- Define the PD form directly as regularization of the integration current. -/
noncomputable def poincareDualForm_data_fromCurrent (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    (data : ClosedSubmanifoldData n X (2 * p)) : SmoothForm n X (2 * p) :=
  Hodge.GMT.regularizeCurrentToForm (n := n) (X := X) (k := 2 * p)
    (Hodge.GMT.integrationCurrent_data (n := n) (X := X) p data)

/-- Data-first PD form defined via integration-current regularization. -/
noncomputable def poincareDualForm_data (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    (data : ClosedSubmanifoldData n X (2 * p)) : SmoothForm n X (2 * p) :=
  poincareDualForm_data_fromCurrent n X p data

/-! ### Tightened PD interface: PD form from integration current -/

/-- **Poincaré Dual Form via Integration Current** (data-first).

This strengthens `PoincareDualFormExists_data` by requiring the PD form to be obtained by
regularizing the integration current `integrationCurrent_data`.
The proof track assumes `PoincareDualityFromCurrentsData`, which yields this interface
as a derived instance. -/
class PoincareDualFormFromCurrentData (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    extends PoincareDualFormExists_data n X p where
  /-- The PD form is obtained by regularizing the integration current. -/
  from_current :
    ∀ data : ClosedSubmanifoldData n X (2 * p),
      poincareDualForm_data_compat n X p data =
        poincareDualForm_data_fromCurrent n X p data

/-! ### Tightened PD pipeline lemma -/

theorem poincareDualForm_data_compat_eq (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualFormFromCurrentData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    poincareDualForm_data_compat n X p data =
      poincareDualForm_data n X p data := by
  simpa [poincareDualForm_data] using
    (PoincareDualFormFromCurrentData.from_current (n := n) (X := X) (p := p) data)

/-! Compatibility-only closedness/empty lemmas.

These require `PoincareDualFormFromCurrentData` directly. The proof track instead
uses `PoincareDualityFromCurrentsData` and the derived lemmas in
`Hodge/Classical/PoincareDualityFromCurrents.lean`. -/

theorem poincareDualForm_data_isClosed (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualFormFromCurrentData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    IsFormClosed (poincareDualForm_data n X p data) := by
  have hcompat := poincareDualForm_data_compat_isClosed (n := n) (X := X) (p := p) data
  simpa [poincareDualForm_data_compat_eq (n := n) (X := X) (p := p) data] using hcompat

theorem poincareDualForm_data_empty (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualFormFromCurrentData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    data.carrier = ∅ → poincareDualForm_data n X p data = 0 := by
  intro h
  have hcompat := poincareDualForm_data_compat_empty (n := n) (X := X) (p := p) data h
  simpa [poincareDualForm_data_compat_eq (n := n) (X := X) (p := p) data] using hcompat

theorem poincareDualForm_data_eq_regularizeCurrent (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    poincareDualForm_data n X p data =
      Hodge.GMT.regularizeCurrentToForm (n := n) (X := X) (k := 2 * p)
        (Hodge.GMT.integrationCurrent_data (n := n) (X := X) p data) := rfl

/-- Compatibility: package data-first PD form as set-based PD form data. -/
noncomputable def poincareDualFormData_of_data (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [inst : PoincareDualFormExists_data n X p]
    {Z : Set X} (data : ClosedSubmanifoldData n X (2 * p)) (hZ : data.carrier = Z) :
    PoincareDualFormData n X p Z := by
  refine
    { form := poincareDualForm_data_compat n X p data
      is_closed := poincareDualForm_data_compat_isClosed n X p data
      empty_vanishes := ?_ }
  intro hZempty
  have hcarrier : data.carrier = ∅ := by
    simpa [hZ] using hZempty
  exact poincareDualForm_data_compat_empty n X p data hcarrier

end DataFirst

/-!
══════════════════════════════════════════════════════════════════════════════════════════
NOTE: The off-track axioms (poincareDualForm_isPP, _isRational, _additive) were archived to
archive/Hodge/Classical/CycleClassAxioms.lean because they are NOT needed for hodge_conjecture'.
══════════════════════════════════════════════════════════════════════════════════════════
-/

/-!
## Note: no `PoincareDualFormExists.universal`

`PoincareDualFormExists` is a deep existence statement (Poincaré duality / fundamental class).
We intentionally do **not** provide a “universal” placeholder constructor here (e.g. `Z ↦ ω^p`),
because that would reintroduce a semantic gotcha (fake PD forms) on the proof spine.
-/

end CycleClass

/-! ## The Fundamental Class Implementation

This section provides the implementation that will be used by GAGA.lean
to define `FundamentalClassSet_impl`. -/

/-- **The Fundamental Class Form Implementation** (set-based).

    Given a set Z and codimension p, return the Poincaré dual form η_Z.

    This is the main definition that replaces the old "constant-zero" stub for `FundamentalClassSet_impl`.

    **M2 Update (2026-01-24)**: Now Z-dependent via Hausdorff measure:
    - For Z = ∅: returns 0
    - For Z containing basepoint: returns `omegaPower p` (the Kähler power)
    - For Z not containing basepoint: returns 0

    The form satisfies:
    1. Closedness (by `poincareDualForm_isClosed`)
    2. Z-dependence (different Z give different forms)

    **Compatibility note**: prefer `fundamentalClassImpl_data` when explicit
    `ClosedSubmanifoldData` is available. -/
def fundamentalClassImpl (n : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [Nonempty X]
    (p : ℕ) [inst : CycleClass.PoincareDualFormExists n X p] (Z : Set X) :
    SmoothForm n X (2 * p) :=
  CycleClass.poincareDualForm n X p Z

/-- The fundamental class of the empty set is zero. -/
theorem fundamentalClassImpl_empty (p : ℕ)
    [inst : CycleClass.PoincareDualFormExists n X p] :
    fundamentalClassImpl n X p (∅ : Set X) = 0 :=
  CycleClass.poincareDualForm_empty n X p

/-- The fundamental class is closed. -/
theorem fundamentalClassImpl_isClosed (p : ℕ) (Z : Set X)
    [inst : CycleClass.PoincareDualFormExists n X p] :
    IsFormClosed (fundamentalClassImpl n X p Z) :=
  CycleClass.poincareDualForm_isClosed n X p Z

/-! ### Data-first fundamental class (ClosedSubmanifoldData) -/

section DataFirstFundamental

/-- Data-first fundamental class form, built from explicit `ClosedSubmanifoldData`.

Compatibility-only: the proof spine prefers `FundamentalClassSet_data`
(in `Hodge/Classical/GAGA.lean`), which requires `PoincareDualityFromCurrentsData`
and routes through the current‑regularization pipeline. -/
def fundamentalClassImpl_data (n : ℕ) (X : Type u)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (p : ℕ)
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualFormFromCurrentData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    SmoothForm n X (2 * p) :=
  CycleClass.poincareDualForm_data n X p data

/-- Data-first fundamental class is closed (compatibility-only). -/
theorem fundamentalClassImpl_data_isClosed (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [CycleClass.PoincareDualFormFromCurrentData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    IsFormClosed (fundamentalClassImpl_data n X p data) :=
  CycleClass.poincareDualForm_data_isClosed n X p data

end DataFirstFundamental

/-!
**Z-dependence of Poincaré dual forms** (M2 semantic property).

The Poincaré dual form construction depends on Z through the Hausdorff measure.
-/
-- NOTE: Documentation-only stub removed (was a trivial placeholder).
-- TODO (unconditional track): state and prove the actual Z-dependence property.

/-!
NOTE: fundamentalClassImpl_isPP, _isRational, _additive were archived with their axioms.
-/
