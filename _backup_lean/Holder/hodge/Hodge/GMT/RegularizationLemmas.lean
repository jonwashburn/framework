import Hodge.GMT.HeatKernelRegularization
import Hodge.Classical.CycleClass

/-!
# Regularization Lemmas (Checklist)

This file collects the **lemmas** required to discharge
`CycleClass.PoincareDualityFromCurrentsData` (and hence
`CycleClass.PoincareDualFormFromCurrentData`) from a concrete regularization.

No stubs or axioms are introduced here; this is a checklist and placeholder
namespace for the eventual proofs.

## Lemma Checklist (to implement)

1. **Closedness for cycles**
   - `regularizeCurrentToForm_isClosed`:
     If `T` is a cycle, then `regularizeCurrentToForm T` is closed.

2. **Empty‑carrier vanishing**
   - `regularizeCurrentToForm_empty`:
     If the integration current of a closed submanifold is zero (empty carrier),
     then its regularized form is zero.

3. **Compatibility with integration current**
   - `poincareDualForm_data_eq_regularizeCurrent` is already definitional,
     but use these lemmas to build a `PoincareDualityFromCurrentsData` instance
     (which yields `PoincareDualFormFromCurrentData`).

4. **Support control (optional, but useful)**
   - Regularization does not enlarge support beyond a controlled neighborhood.

These lemmas should live in `Hodge/GMT/RegularizationLemmas.lean` and be used
to instantiate `CycleClass.PoincareDualityFromCurrentsData`.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.GMT

/-!
## Concrete Regularization Lemmas (Data Interface)

This class records the **concrete lemma targets** needed to discharge
`CycleClass.PoincareDualityFromCurrentsData` from an explicit regularization
pipeline. It is *not* an axiom: users must provide instances.
-/

class CurrentRegularizationLemmas (n : ℕ) (X : Type*) (p : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X]
    [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    [CurrentRegularizationData n X (2 * p)] : Type where
  /-- Closedness of the regularized integration current. -/
  poincareDualForm_data_isClosed :
    ∀ data : ClosedSubmanifoldData n X (2 * p),
      IsFormClosed (CycleClass.poincareDualForm_data n X p data)
  /-- Empty carrier gives zero. -/
  poincareDualForm_data_empty :
    ∀ data : ClosedSubmanifoldData n X (2 * p),
      data.carrier = ∅ → CycleClass.poincareDualForm_data n X p data = 0

end Hodge.GMT
