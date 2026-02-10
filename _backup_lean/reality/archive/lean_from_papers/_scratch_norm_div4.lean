import Mathlib

example (S : ℂ) : ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / Real.sqrt 8 := by
  have hnorm_sqrt8 : ‖(Real.sqrt 8 : ℂ)‖ = Real.sqrt 8 := by
    have hsqrt8_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt8_nonneg : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt hsqrt8_pos
    have : ‖(Real.sqrt 8 : ℂ)‖ = |Real.sqrt 8| := by
      simpa using (RCLike.norm_ofReal (K := ℂ) (Real.sqrt 8))
    simpa [abs_of_nonneg hsqrt8_nonneg] using this
  -- now
  -- norm_div gives denom norm
  have : ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / ‖(Real.sqrt 8 : ℂ)‖ := by
    simpa using (norm_div S (Real.sqrt 8 : ℂ))
  -- rewrite denom norm
  simpa [hnorm_sqrt8] using this
