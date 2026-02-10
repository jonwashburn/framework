import Mathlib.Analysis.InnerProductSpace.Pi_L2

open scoped BigOperators

example : InnerProductSpace ℂ (Fin 8 → ℂ) := by
  infer_instance
