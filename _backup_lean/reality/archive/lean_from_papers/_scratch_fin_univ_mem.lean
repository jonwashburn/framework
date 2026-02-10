import Mathlib

example : ((0 : Fin 8) ∈ (Finset.univ : Finset (Fin 8))) := by
  decide
