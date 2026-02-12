import Hodge.Classical.CycleClass
import Hodge.GMT.RegularizationLemmas

/-!
# Poincaré Duality From Currents (Instance Plumbing)

This module provides the **instance construction path** from a concrete
current-regularization theory to the data‑first PD interface:

```
CurrentRegularizationData + PD regularization lemmas
      ⇒ PoincareDualityFromCurrentsData
      ⇒ PoincareDualFormFromCurrentData
```

No stubs or axioms are introduced: users must supply the closedness/empty‑set
lemmas for the regularized integration current. It also provides a
data‑first fundamental class helper (`fundamentalClassImpl_data_fromCurrents`)
used by the GAGA layer.
-/

noncomputable section

open Classical Hodge

set_option autoImplicit false

namespace CycleClass

universe u

/-- **Poincaré duality from currents** (data-first).

This records the two concrete properties needed to build
`PoincareDualFormFromCurrentData` from the explicit regularization pipeline:

- the regularized integration current is closed;
- empty carrier gives the zero form.
-/
class PoincareDualityFromCurrentsData (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)] : Type where
  /-- The regularized integration current is closed. -/
  isClosed :
    ∀ data : ClosedSubmanifoldData n X (2 * p),
      IsFormClosed (poincareDualForm_data n X p data)
  /-- Empty carrier gives the zero PD form. -/
  empty_vanishes :
    ∀ data : ClosedSubmanifoldData n X (2 * p),
      data.carrier = ∅ → poincareDualForm_data n X p data = 0

/-! ### Derived lemmas (data-first route) -/

theorem poincareDualForm_data_isClosed_ofCurrents (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    IsFormClosed (poincareDualForm_data n X p data) :=
  PoincareDualityFromCurrentsData.isClosed (n := n) (X := X) (p := p) data

theorem poincareDualForm_data_empty_ofCurrents (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) (h : data.carrier = ∅) :
    poincareDualForm_data n X p data = 0 :=
  PoincareDualityFromCurrentsData.empty_vanishes (n := n) (X := X) (p := p) data h

/-! ### Fundamental class built from the current-regularization pipeline -/

/-- Data-first fundamental class: use the regularized integration current. -/
noncomputable def fundamentalClassImpl_data_fromCurrents (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    SmoothForm n X (2 * p) :=
  poincareDualForm_data n X p data

/-- Closedness of the data-first fundamental class (from currents). -/
theorem fundamentalClassImpl_data_isClosed_ofCurrents (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) :
    IsFormClosed (fundamentalClassImpl_data_fromCurrents n X p data) :=
  PoincareDualityFromCurrentsData.isClosed (n := n) (X := X) (p := p) data

/-- Empty carrier gives the zero data-first fundamental class (from currents). -/
theorem fundamentalClassImpl_data_empty_ofCurrents (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualityFromCurrentsData n X p]
    (data : ClosedSubmanifoldData n X (2 * p)) (h : data.carrier = ∅) :
    fundamentalClassImpl_data_fromCurrents n X p data = 0 :=
  PoincareDualityFromCurrentsData.empty_vanishes (n := n) (X := X) (p := p) data h

/-- Build `PoincareDualityFromCurrentsData` from the regularization lemma package. -/
noncomputable instance instPoincareDualityFromCurrentsData_ofRegularizationLemmas
    (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [Hodge.GMT.CurrentRegularizationLemmas n X p] :
    PoincareDualityFromCurrentsData n X p :=
  { isClosed :=
      Hodge.GMT.CurrentRegularizationLemmas.poincareDualForm_data_isClosed
        (n := n) (X := X) (p := p)
    empty_vanishes :=
      Hodge.GMT.CurrentRegularizationLemmas.poincareDualForm_data_empty
        (n := n) (X := X) (p := p) }

/-- Build `PoincareDualFormFromCurrentData` from the concrete current‑regularization lemmas. -/
noncomputable def poincareDualFormFromCurrentData_ofCurrents (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualityFromCurrentsData n X p] :
    PoincareDualFormFromCurrentData n X p :=
  { choose := fun data =>
      { form := poincareDualForm_data n X p data
        is_closed := PoincareDualityFromCurrentsData.isClosed (n := n) (X := X) (p := p) data
        empty_vanishes :=
          PoincareDualityFromCurrentsData.empty_vanishes (n := n) (X := X) (p := p) data }
    from_current := by
      intro data
      rfl }

/-- Instance: the concrete current-regularization lemmas yield the data‑first PD interface. -/
noncomputable instance instPoincareDualFormFromCurrentData_ofCurrents (n : ℕ) (X : Type u) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [Hodge.GMT.CurrentRegularizationData n X (2 * p)]
    [PoincareDualityFromCurrentsData n X p] :
    PoincareDualFormFromCurrentData n X p :=
  poincareDualFormFromCurrentData_ofCurrents (n := n) (X := X) (p := p)

end CycleClass
