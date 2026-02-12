import Mathlib.Analysis.Distribution.TestFunction

open scoped BoundedContinuousFunction

namespace ScratchBCFMap

open Classical

variable {α β γ : Type*} [TopologicalSpace α]
variable [PseudoMetricSpace β] [PseudoMetricSpace γ]

#check BoundedContinuousFunction
#check BoundedContinuousFunction.map
#check BoundedContinuousFunction.comp

end ScratchBCFMap
