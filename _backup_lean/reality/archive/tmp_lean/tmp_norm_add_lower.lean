import Mathlib

example (z : ℂ) : (1 : ℝ) - ‖z‖ ≤ ‖(1 : ℂ) + z‖ := by
  have : (1:ℂ) = ((1:ℂ) + z) - z := by ring
  have h' : ‖(1:ℂ)‖ ≤ ‖(1:ℂ) + z‖ + ‖z‖ := by
    simpa [this] using (norm_sub_le ((1:ℂ) + z) z)
  have h'' : (1:ℝ) ≤ ‖(1:ℂ) + z‖ + ‖z‖ := by
    -- rewrite `‖(1:ℂ)‖` as 1
    simpa [norm_one] using h'
  -- subtract ‖z‖ (note: `sub_le_iff_le_add` expects `a - b ≤ c ↔ a ≤ c + b`)
  -- So we want: 1 - ‖z‖ ≤ ‖1+z‖  from  1 ≤ ‖1+z‖ + ‖z‖.
  exact sub_le_iff_le_add.2 (by simpa [add_comm, add_left_comm, add_assoc] using h'')
