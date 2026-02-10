
import Mathlib
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Constants

open IndisputableMonolith.Constants

def check_alpha : IO Unit := do
  let phi_val := (1 + Real.sqrt 5) / 2
  let seed := 4 * Real.pi * 11
  let gap := w8_from_eight_tick * Real.log phi_val
  let kappa := -103.0 / (102.0 * Real.pi ^ 5)
  let alpha_inv_calc := seed - (gap + kappa)

  IO.println s!"Phi: {phi_val}"
  IO.println s!"Seed (4pi*11): {seed}"
  IO.println s!"Gap (w8 * ln phi): {gap}"
  IO.println s!"Kappa correction: {kappa}"
  IO.println s!"Calculated Alpha Inverse: {alpha_inv_calc}"
  IO.println s!"Target: 137.035999"
  IO.println s!"Difference: {alpha_inv_calc - 137.035999}"
