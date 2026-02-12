import Hodge.Basic

namespace ScratchFiberAltRealCLM

open Classical

variable {n k : ℕ}

-- Does FiberAlt n k have a NormedSpace ℝ instance?
#check (inferInstance : NormedSpace ℝ (FiberAlt n k))

-- Can we form a real ContinuousLinearMap between fibers?
#check (FiberAlt n k →L[ℝ] FiberAlt n k)

end ScratchFiberAltRealCLM
