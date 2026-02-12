import Mathlib

open scoped BigOperators

#check IsROrC
#check Orthonormal
#check inner_sum_right
#check inner_sum_left

-- check we have an inner product on functions
example : InnerProductSpace ℂ (Fin 8 → ℂ) := by
  infer_instance
