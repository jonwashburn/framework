import Hodge.Analytic.DistributionTestForms

import Mathlib.Analysis.Distribution.TestFunction

/-!
# Stage 1 (Euclidean model): Currents as continuous linear maps on LF test forms

This module is a **Stage 1** building block: in Euclidean domains we can model “currents”
as continuous linear maps on the LF space of compactly supported smooth test forms.

This is the direction required by `tex/archive/HodgePlan-mc-28.1.26.rtf` (Stages 1–3), and it
leverages Mathlib’s distribution/test-function infrastructure.

For now we only record the core type definition and basic algebraic structure.
-/

noncomputable section

open Classical TopologicalSpace

namespace Hodge

open scoped Distributions

namespace EuclidCurrent

-- The additive and scalar structures are inherited from `ContinuousLinearMap`.
example {n k : ℕ} {Ω : TopologicalSpace.Opens (Euclid n)} :
    AddCommGroup (EuclidCurrent n k Ω) := by infer_instance

example {n k : ℕ} {Ω : TopologicalSpace.Opens (Euclid n)} :
    SMul ℝ (EuclidCurrent n k Ω) := by infer_instance

end EuclidCurrent

end Hodge

end
