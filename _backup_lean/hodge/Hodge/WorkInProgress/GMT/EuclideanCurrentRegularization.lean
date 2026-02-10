import Hodge.Analytic.Currents
import Hodge.Analytic.Forms
import Hodge.WorkInProgress.GMT.EuclideanMollifier
import Hodge.WorkInProgress.Instances.EuclideanManifold

noncomputable section

open Classical

namespace Hodge.GMT

universe u

variable {n : ℕ} {k : ℕ}

/-- WIP interface: regularize currents on the Euclidean model space. -/
class EuclideanCurrentRegularizationData (n : ℕ) (k : ℕ) : Type where
  regularize : Current n (TangentModel n) k → SmoothForm n (TangentModel n) k

/-- Regularize a current on the Euclidean model space (WIP). -/
noncomputable def regularizeCurrentEuclidean
    [EuclideanCurrentRegularizationData n k]
    (T : Current n (TangentModel n) k) : SmoothForm n (TangentModel n) k :=
  EuclideanCurrentRegularizationData.regularize (n := n) (k := k) T

instance instEuclideanCurrentRegularizationData (n : ℕ) (k : ℕ) :
    EuclideanCurrentRegularizationData n k := by
  classical
  -- TODO: define by chartwise convolution on coefficients and verify smoothness.
  refine ⟨?_⟩
  intro T
  sorry

end Hodge.GMT
