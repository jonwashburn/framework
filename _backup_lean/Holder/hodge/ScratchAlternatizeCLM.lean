import Hodge.Analytic.DistributionTestForms

open scoped Distributions

namespace ScratchAlternatizeCLM

open Classical TopologicalSpace

variable {n k : ℕ}

-- check type of alternatizeUncurryFinCLM
#check ContinuousAlternatingMap.alternatizeUncurryFinCLM

-- specialize to get a CLM from (TangentModel n →L[ℂ] FiberAlt n k) to FiberAlt n (k+1)
#check (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (TangentModel n) ℂ (n := k))

end ScratchAlternatizeCLM
