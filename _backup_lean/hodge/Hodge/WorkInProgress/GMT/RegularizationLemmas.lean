import Hodge.GMT.RegularizationLemmas

noncomputable section

open Classical Hodge

namespace Hodge.GMT

variable {n : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

instance instCurrentRegularizationLemmas {p : ℕ}
    [CurrentRegularizationData n X (2 * p)] :
    CurrentRegularizationLemmas n X p where
  poincareDualForm_data_isClosed := fun data => by
    -- Proof that regularization of a cycle is closed.
    -- Requires commuting regularization with d.
    sorry
  poincareDualForm_data_empty := fun data h => by
    -- Proof that regularization of empty/support-zero current is zero.
    sorry

end Hodge.GMT
