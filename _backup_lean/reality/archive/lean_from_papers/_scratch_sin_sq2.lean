import Mathlib

open Real

example : (Real.sin (Real.pi/8))^2 = (2 - Real.sqrt 2) / 4 := by
  rw [Real.sin_pi_div_eight]
  have hnonneg : 0 ≤ (2 - Real.sqrt 2) := by
    have hs : Real.sqrt 2 < (3/2 : ℝ) := Real.sqrt_two_lt_three_halves
    nlinarith [hs]
  -- unfold square
  simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Real.sq_sqrt hnonneg]
