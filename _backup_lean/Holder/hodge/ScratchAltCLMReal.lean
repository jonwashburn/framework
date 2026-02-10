import Hodge.Basic

namespace ScratchAltCLMReal

open Classical

variable {n k : ℕ}

abbrev FiberAltR (n : ℕ) (k : ℕ) := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ

#check (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (TangentModel n) ℂ (n := k))
-- expects (E →L[ℝ] E[⋀^Fin k]→L[ℝ] ℂ) ->L[ℝ] E[⋀^(k+1)]→L[ℝ] ℂ

end ScratchAltCLMReal
