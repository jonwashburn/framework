import Mathlib
import IndisputableMonolith.Constants.GapWeight.Formula
import IndisputableMonolith.Numerics.Interval.PhiBounds

namespace IndisputableMonolith.Constants.GapWeight

open Complex
open scoped BigOperators
open IndisputableMonolith.LightLanguage.Basis
open IndisputableMonolith.Numerics

-- We'll try to prove a coarse bound: 38 < phiDFTAmplitude 1

lemma phiDFTAmplitude_one_gt_38 : (38 : ℝ) < phiDFTAmplitude (1 : Fin 8) := by
  -- Let z = ω⁷ φ
  let z : ℂ := omega8 ^ 7 * (phi : ℂ)
  -- The DFT coefficient is a geometric sum divided by √8
  have h_coeff : phiDFTCoeff (1 : Fin 8) = (∑ t : Fin 8, z ^ t.val) / (Real.sqrt 8 : ℂ) := by
    -- use the helper lemma we can re-prove quickly
    unfold phiDFTCoeff dft8_entry phiPatternComplex phiPattern
    rw [Finset.sum_div]
    congr 1
    ext t
    -- simplify to (ω⁷φ)^t / √8
    simp [z, dft8_entry, star_div₀, star_pow, star_omega8, omega8_inv_eq_pow7, Nat.mul_one, mul_pow]
    simp [div_mul_eq_mul_div, mul_div, mul_assoc, mul_left_comm, mul_comm]
  -- Now bound the norm of the sum using the telescoping identity
  have h_geom : (∑ t : Fin 8, z ^ t.val) * (z - 1) = z ^ 8 - 1 := by
    have h8 : (∑ t : Fin 8, z ^ t.val) = z^0 + z^1 + z^2 + z^3 + z^4 + z^5 + z^6 + z^7 := by
      simp only [Fin.sum_univ_eight]
      rfl
    rw [h8]
    ring
  -- Work with norms
  have h_norm_mul : ‖(∑ t : Fin 8, z ^ t.val)‖ * ‖z - 1‖ = ‖z ^ 8 - 1‖ := by
    -- take norms of `h_geom`
    -- `‖a*b‖ = ‖a‖*‖b‖`
    simpa [h_geom] using congrArg (fun w : ℂ => ‖w‖) h_geom
  -- That attempt likely isn't right; let's do it properly.
  admit

end IndisputableMonolith.Constants.GapWeight
