import Mathlib
import IndisputableMonolith.Constants.GapWeight.Formula
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.Numerics.Interval.PhiBounds

namespace IndisputableMonolith.Constants.GapWeight

open Complex
open scoped BigOperators
open IndisputableMonolith.LightLanguage.Basis
open IndisputableMonolith.Numerics

-- helper: norm of z = omega8^7 * phi
lemma norm_omega7_mul_phi : ‖(omega8 ^ 7 * (phi : ℂ))‖ = phi := by
  have hω : ‖omega8 ^ 7‖ = (1 : ℝ) := by
    have : ‖omega8 ^ 7‖ = ‖omega8‖ ^ 7 := by
      simpa using (Complex.norm_pow omega8 7)
    simpa [this, omega8_abs]
  have hphi_nonneg : (0 : ℝ) ≤ phi := le_of_lt phi_pos
  calc
    ‖omega8 ^ 7 * (phi : ℂ)‖ = ‖omega8 ^ 7‖ * ‖(phi : ℂ)‖ := by
      simpa using (norm_mul (omega8 ^ 7) (phi : ℂ))
    _ = 1 * phi := by
      have : ‖(phi : ℂ)‖ = phi := by
        have : ‖(phi : ℂ)‖ = |phi| := by
          simpa using (RCLike.norm_ofReal (K := ℂ) phi)
        simpa [abs_of_pos phi_pos] using this
      simp [hω, this, hphi_nonneg]
    _ = phi := by ring

/-- Coarse lower bound: `phiDFTAmplitude 1 > 38`. -/
lemma phiDFTAmplitude_one_gt_38 : (38 : ℝ) < phiDFTAmplitude (1 : Fin 8) := by
  -- Let z = ω⁷ φ and S = ∑ z^t.
  let z : ℂ := omega8 ^ 7 * (phi : ℂ)
  let S : ℂ := ∑ t : Fin 8, z ^ t.val

  -- DFT coefficient c1 = S / √8
  have h_coeff : phiDFTCoeff (1 : Fin 8) = S / (Real.sqrt 8 : ℂ) := by
    unfold phiDFTCoeff dft8_entry phiPatternComplex phiPattern
    rw [Finset.sum_div]
    -- after unfolding, each summand is `star(dft8_entry t 1) * (phi^t)`
    -- and simplifies to `(ω⁷φ)^t / √8`.
    simp [S, z, dft8_entry, phiPatternComplex, phiPattern, star_div₀, star_pow, star_omega8,
      omega8_inv_eq_pow7, Nat.mul_one, mul_pow]
    simp [div_mul_eq_mul_div, mul_div, mul_assoc, mul_left_comm, mul_comm]

  -- telescoping identity: S*(z-1) = z^8 - 1
  have h_sum_geom : S * (z - 1) = z ^ 8 - 1 := by
    have h8 : S = z^0 + z^1 + z^2 + z^3 + z^4 + z^5 + z^6 + z^7 := by
      simp [S, Fin.sum_univ_eight]
    rw [h8]
    ring

  -- take norms: ‖S‖ * ‖z-1‖ = ‖z^8 - 1‖
  have hnorm : ‖S‖ * ‖z - 1‖ = ‖z ^ 8 - 1‖ := by
    have := congrArg (fun w : ℂ => ‖w‖) h_sum_geom
    simpa [norm_mul] using this

  -- bounds on numerator and denominator
  have hz_norm : ‖z‖ = phi := by
    simpa [z] using norm_omega7_mul_phi
  have hden_le : ‖z - 1‖ ≤ phi + 1 := by
    simpa [hz_norm] using (norm_sub_le z (1 : ℂ))
  have hnum_ge : (phi ^ 8 - 1) ≤ ‖z ^ 8 - 1‖ := by
    have h := norm_sub_norm_le (z ^ 8) (1 : ℂ)
    have hz8_norm : ‖z ^ 8‖ = phi ^ 8 := by
      simpa [hz_norm] using (norm_pow z 8)
    simpa [hz8_norm] using h

  have hden_pos : (0 : ℝ) < ‖z - 1‖ := by
    have hz_ne_one : z ≠ (1 : ℂ) := by
      intro hz1
      have : ‖z‖ = ‖(1 : ℂ)‖ := by simpa [hz1]
      have : phi = (1 : ℝ) := by simpa [hz_norm] using this
      exact phi_ne_one this
    have : z - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne_one
    simpa [norm_pos_iff] using this

  -- lower bound on ‖S‖
  have hS_ge : (phi ^ 8 - 1) / (phi + 1) ≤ ‖S‖ := by
    have hS_eq : ‖S‖ = ‖z ^ 8 - 1‖ / ‖z - 1‖ := by
      have hden_ne : ‖z - 1‖ ≠ 0 := ne_of_gt hden_pos
      exact (eq_div_iff hden_ne).2 (by simpa [mul_comm] using hnorm)
    rw [hS_eq]
    have h1 : (phi ^ 8 - 1) / ‖z - 1‖ ≤ ‖z ^ 8 - 1‖ / ‖z - 1‖ := by
      have hden_nonneg : (0 : ℝ) ≤ ‖z - 1‖ := le_of_lt hden_pos
      exact div_le_div_of_nonneg_right hden_nonneg hnum_ge
    have h2 : (phi ^ 8 - 1) / (phi + 1) ≤ (phi ^ 8 - 1) / ‖z - 1‖ := by
      have hnum_nonneg : (0 : ℝ) ≤ phi ^ 8 - 1 := by
        have hgt : (1 : ℝ) < phi ^ 8 := one_lt_pow₀ one_lt_phi (by norm_num)
        linarith
      have hinv : (1 : ℝ) / (phi + 1) ≤ (1 : ℝ) / ‖z - 1‖ :=
        one_div_le_one_div_of_le hden_pos hden_le
      have := mul_le_mul_of_nonneg_left hinv hnum_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    exact le_trans h2 (le_trans h1 (le_rfl))

  -- convert to amplitude bound
  unfold phiDFTAmplitude
  -- `normSq` is norm^2
  simp [h_coeff, Complex.normSq_eq_norm_sq]

  have hsqrt8_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt8_nonneg : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt hsqrt8_pos

  have hcoeff_norm_ge : (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) ≤ ‖S / (Real.sqrt 8 : ℂ)‖ := by
    have hnorm_sqrt8 : ‖(Real.sqrt 8 : ℂ)‖ = Real.sqrt 8 := by
      have : ‖(Real.sqrt 8 : ℂ)‖ = |Real.sqrt 8| := by
        simpa using (RCLike.norm_ofReal (K := ℂ) (Real.sqrt 8))
      simpa [abs_of_nonneg hsqrt8_nonneg] using this
    have hnorm_div : ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / Real.sqrt 8 := by
      simpa [hnorm_sqrt8] using (norm_div S (Real.sqrt 8 : ℂ))
    rw [hnorm_div]
    have : (phi ^ 8 - 1) / (phi + 1) / Real.sqrt 8 ≤ ‖S‖ / Real.sqrt 8 :=
      div_le_div_of_nonneg_right hsqrt8_nonneg hS_ge
    simpa [div_div, mul_assoc, mul_left_comm, mul_comm] using this

  have hcoeff_sq_ge : ((phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8))^2 ≤ (‖S / (Real.sqrt 8 : ℂ)‖)^2 := by
    have hL_nonneg : (0 : ℝ) ≤ (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) := by
      have hnum_nonneg : (0 : ℝ) ≤ phi ^ 8 - 1 := by
        have hgt : (1 : ℝ) < phi ^ 8 := one_lt_pow₀ one_lt_phi (by norm_num)
        linarith
      have hden_pos : (0 : ℝ) < (phi + 1) * Real.sqrt 8 := by
        have : (0 : ℝ) < phi + 1 := by linarith [phi_pos]
        exact mul_pos this hsqrt8_pos
      exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
    exact pow_le_pow_left₀ hL_nonneg hcoeff_norm_ge 2

  -- numeric lower bound on the LHS using φ-bounds
  have hphi8_gt : (46.97 : ℝ) < phi ^ 8 := by
    have h : (46.97 : ℝ) < Real.goldenRatio ^ 8 := Numerics.phi_pow8_gt
    simpa [IndisputableMonolith.Constants.phi] using h
  have hphi1_lt : phi + 1 < (2.62 : ℝ) := by
    have hφ_lt : phi < (1.62 : ℝ) := phi_lt_onePointSixTwo
    linarith

  have hL_gt_38 : (38 : ℝ) < ((phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8))^2 := by
    -- a crude bound: replace φ^8 by 46.97 and φ+1 by 2.62
    have h : (38 : ℝ) < ((45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8))^2 := by
      norm_num
    have hnum_gt : (45.97 : ℝ) < phi ^ 8 - 1 := by linarith [hphi8_gt]
    have hden_lt : (phi + 1) * Real.sqrt 8 < (2.62 : ℝ) * Real.sqrt 8 :=
      mul_lt_mul_of_pos_right hphi1_lt hsqrt8_pos
    -- show the fraction is larger than the crude one
    have hfrac_gt : (45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8) < (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) := by
      -- cross-multiply
      have hposA : (0 : ℝ) < (2.62 : ℝ) * Real.sqrt 8 := by
        have : (0 : ℝ) < (2.62 : ℝ) := by norm_num
        exact mul_pos this hsqrt8_pos
      have hposB : (0 : ℝ) < (phi + 1) * Real.sqrt 8 := by
        have : (0 : ℝ) < phi + 1 := by linarith [phi_pos]
        exact mul_pos this hsqrt8_pos
      -- use `div_lt_div_iff` isn't available; rewrite and use `nlinarith`
      have hcross : (45.97 : ℝ) * ((phi + 1) * Real.sqrt 8) < (phi ^ 8 - 1) * ((2.62 : ℝ) * Real.sqrt 8) := by
        have hA := mul_lt_mul_of_pos_right hnum_gt hposB
        have hB := mul_lt_mul_of_pos_left hden_lt (by
          have hgt : (0 : ℝ) < phi ^ 8 - 1 := by
            have hgt' : (1 : ℝ) < phi ^ 8 := one_lt_pow₀ one_lt_phi (by norm_num)
            linarith
          exact hgt)
        exact lt_trans hA hB
      -- finish by nlinarith on inverses
      nlinarith [hcross, hposA, hposB]
    have hfrac_sq_gt : ((45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8))^2 < ((phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8))^2 := by
      have h0 : (0 : ℝ) ≤ (45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8) := by
        exact div_nonneg (by norm_num) (le_of_lt (by
          have : (0 : ℝ) < (2.62 : ℝ) := by norm_num
          exact mul_pos this hsqrt8_pos))
      exact pow_lt_pow_left₀ h0 hfrac_gt 2
    exact lt_trans h (lt_of_lt_of_le hfrac_sq_gt (le_rfl))

  have : (38 : ℝ) < (‖S / (Real.sqrt 8 : ℂ)‖)^2 :=
    lt_of_lt_of_le hL_gt_38 hcoeff_sq_ge
  simpa using this

end IndisputableMonolith.Constants.GapWeight
