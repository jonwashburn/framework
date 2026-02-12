import Hodge.Analytic.DomCoprodComplex

noncomputable section

open scoped TensorProduct

namespace Scratch

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [CompleteSpace ℝ]
variable {k l : ℕ}

#check (ContinuousAlternatingMap.wedgeℂ_linear (E := E) (k := k) (l := l))

end Scratch
