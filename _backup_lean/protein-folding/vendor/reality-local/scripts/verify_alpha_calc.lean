
def check_alpha : IO Unit := do
  let phi_val : Float := (1.0 + Float.sqrt 5.0) / 2.0
  let pi_val : Float := 3.14159265358979323846

  -- Constants from code
  let w8 : Float := 2.488254397846
  let seed : Float := 4.0 * pi_val * 11.0
  let gap : Float := w8 * Float.log phi_val
  let kappa : Float := -103.0 / (102.0 * (Float.pow pi_val 5.0))

  let alpha_inv_calc : Float := seed - (gap + kappa)

  IO.println s!"Phi: {phi_val}"
  IO.println s!"Seed (4pi*11): {seed}"
  IO.println s!"Gap (w8 * ln phi): {gap}"
  IO.println s!"Kappa correction: {kappa}"
  IO.println s!"Calculated Alpha Inverse: {alpha_inv_calc}"
  IO.println s!"Target: 137.035999"
  IO.println s!"Difference: {alpha_inv_calc - 137.035999}"

  -- Check the 'alphaLock' (0.191) for comparison
  let alpha_lock : Float := (1.0 - 1.0 / phi_val) / 2.0
  IO.println s!"Alpha Lock (Geometric): {alpha_lock}"

#eval check_alpha
