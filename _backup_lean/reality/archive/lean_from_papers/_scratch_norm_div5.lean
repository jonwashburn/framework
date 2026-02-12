import Mathlib

example (S : ℂ) : ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / Real.sqrt 8 := by
  have hsqrt8_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt8_nonneg : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt hsqrt8_pos
  calc
    ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / ‖(Real.sqrt 8 : ℂ)‖ := by
      simpa using (norm_div S (Real.sqrt 8 : ℂ))
    _ = ‖S‖ / |Real.sqrt 8| := by
      -- rewrite norm of real cast
      simpa [RCLike.norm_ofReal] using congrArg (fun x : ℝ => ‖S‖ / x) (RCLike.norm_ofReal (K := ℂ) (Real.sqrt 8))
    _ = ‖S‖ / Real.sqrt 8 := by
      simp [abs_of_nonneg hsqrt8_nonneg]
