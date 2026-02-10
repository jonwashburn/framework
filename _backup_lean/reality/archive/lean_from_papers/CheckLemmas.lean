import Mathlib

open scoped BigOperators

-- Finset helpers
#check Finset.mul_sum
#check Finset.sum_mul

-- Orthonormal / basis helpers
#check Orthonormal
#check Orthonormal.linearIndependent
#check OrthonormalBasis
#check OrthonormalBasis.mk
#check Orthonormal.inner_left_right_finset

-- common OrthonormalBasis APIs / lemmas (names may vary across Mathlib versions)
#check OrthonormalBasis.repr
#check OrthonormalBasis.orthonormal
#check OrthonormalBasis.sum_repr
#check OrthonormalBasis.sum_inner_mul_inner
#check OrthonormalBasis.repr_apply_apply
#check OrthonormalBasis.repr_self

-- linear independence → spanning (useful to build OrthonormalBasis from Orthonormal families)
#check LinearIndependent
#check LinearIndependent.span_eq_top_of_card_eq_finrank

-- finrank of EuclideanSpace
example : Module.finrank ℂ (EuclideanSpace ℂ (Fin 8)) = 8 := by
  classical
  simp
