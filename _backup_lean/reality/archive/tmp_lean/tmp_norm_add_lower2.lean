import Mathlib

example (z : ℂ) : (1 : ℝ) - ‖z‖ ≤ ‖(1 : ℂ) + z‖ := by
  have h' : ‖((1:ℂ) + z) - z‖ ≤ ‖(1:ℂ) + z‖ + ‖z‖ := norm_sub_le ((1:ℂ) + z) z
  have h'' : ‖(1:ℂ)‖ ≤ ‖(1:ℂ) + z‖ + ‖z‖ := by
    -- simplify `((1+z) - z)` to `1`
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  have h''' : (1:ℝ) ≤ ‖(1:ℂ) + z‖ + ‖z‖ := by
    simpa [norm_one] using h''
  exact (sub_le_iff_le_add).2 (by simpa [add_comm, add_left_comm, add_assoc] using h''')
