import Mathlib
import IndisputableMonolith.Constants.GapWeight.Formula

namespace IndisputableMonolith.Constants.GapWeight

open Complex
open IndisputableMonolith.LightLanguage.Basis
open scoped BigOperators

-- try to restate the coefficient formula used in the positivity proof
lemma phiDFTCoeff_one_as_geom_sum :
    phiDFTCoeff (1 : Fin 8) = (∑ t : Fin 8, (omega8 ^ 7 * (phi : ℂ)) ^ t.val) / (Real.sqrt 8 : ℂ) := by
  unfold phiDFTCoeff dft8_entry phiPatternComplex phiPattern
  -- goal: sum of star(omega8^(t*1)/√8) * (phi^t) equals ...
  rw [Finset.sum_div]
  congr 1
  ext t
  -- simplify star and rewrite to (omega8^7*phi)^t / √8
  simp [dft8_entry, star_div₀, star_pow, star_omega8, omega8_inv_eq_pow7, Nat.mul_one, mul_pow]
  -- remaining reshuffle
  simp [div_mul_eq_mul_div, mul_div, mul_assoc, mul_left_comm, mul_comm]

end IndisputableMonolith.Constants.GapWeight
