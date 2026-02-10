import Mathlib

example {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℂ) (x : E) (hx : ‖x‖ = (1:ℝ)) : ‖c • x‖ = ‖c‖ := by
  simpa [hx, mul_one] using (norm_smul c x)
