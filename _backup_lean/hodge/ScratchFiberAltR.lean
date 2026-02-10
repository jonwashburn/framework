import Hodge.Basic

namespace ScratchFiberAltR

open Classical

variable {n k : ℕ}

-- Define a candidate real-alternating fiber
abbrev FiberAltR (n : ℕ) (k : ℕ) := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ

#check FiberAltR n k
#check (inferInstance : NormedSpace ℝ (FiberAltR n k))

end ScratchFiberAltR
