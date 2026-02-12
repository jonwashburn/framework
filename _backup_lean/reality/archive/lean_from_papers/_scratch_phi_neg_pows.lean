import Mathlib
import IndisputableMonolith.Constants

open IndisputableMonolith.Constants

lemma phi_zpow_neg1 : phi ^ (-(1:ℤ)) = phi - 1 := by
  -- phi^(-1) = 1/phi
  have h : (phi : ℝ) ^ (-(1:ℤ)) = (phi : ℝ)⁻¹ := by simpa using (zpow_neg_one (phi : ℝ))
  rw [h]
  -- from phi^2 = phi + 1, divide by phi
  have hsq : phi^2 = phi + 1 := phi_sq_eq
  have hphi0 : phi ≠ 0 := phi_ne_zero
  -- multiply both sides of goal by phi
  -- show 1 = (phi-1)*phi
  apply inv_eq_of_mul_inv_eq_one_left
  -- hmm maybe easier: show (phi-1)*phi = 1

  have : (phi - 1) * phi = 1 := by
    -- from phi^2 = phi + 1, rearrange: phi^2 - phi = 1 => phi*(phi-1)=1
    have : phi^2 - phi = 1 := by linarith [hsq]
    -- factor
    -- phi^2 - phi = phi*(phi-1)
    have : phi * (phi - 1) = 1 := by
      -- ring
      nlinarith [hsq]
    -- commute
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- now finish inv = phi-1
  -- (phi - 1) * phi = 1 implies (phi-1) = 1/phi
  exact (inv_eq_of_mul_inv_eq_one_left ?_) 
