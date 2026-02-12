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
  have hφ : ‖(phi : ℂ)‖ = phi := by
    have : ‖(phi : ℂ)‖ = |phi| := by
      simpa using (RCLike.norm_ofReal (K := ℂ) phi)
    simpa [abs_of_pos phi_pos] using this
  calc
    ‖omega8 ^ 7 * (phi : ℂ)‖ = ‖omega8 ^ 7‖ * ‖(phi : ℂ)‖ := by
      simpa using (norm_mul (omega8 ^ 7) (phi : ℂ))
    _ = 1 * phi := by simp [hω, hφ, hphi_nonneg]
    _ = phi := by ring

/-- Coarse lower bound: `phiDFTAmplitude 1 > 38`. -/
lemma phiDFTAmplitude_one_gt_38 : (38 : ℝ) < phiDFTAmplitude (1 : Fin 8) := by
  let z : ℂ := omega8 ^ 7 * (phi : ℂ)
  let S : ℂ := ∑ t : Fin 8, z ^ t.val

  -- DFT coefficient c1 = S / √8
  have h_coeff : phiDFTCoeff (1 : Fin 8) = S / (Real.sqrt 8 : ℂ) := by
    unfold phiDFTCoeff dft8_entry phiPatternComplex phiPattern
    rw [Finset.sum_div]
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
    -- from hnorm we get ‖S‖ = ‖z^8-1‖ / ‖z-1‖
    have hS_eq : ‖S‖ = ‖z ^ 8 - 1‖ / ‖z - 1‖ := by
      have hden_ne : ‖z - 1‖ ≠ 0 := ne_of_gt hden_pos
      exact (eq_div_iff hden_ne).2 (by simpa [mul_comm] using hnorm)
    rw [hS_eq]
    -- (phi^8-1)/‖z-1‖ ≤ ‖z^8-1‖/‖z-1‖
    have h1 : (phi ^ 8 - 1) / ‖z - 1‖ ≤ ‖z ^ 8 - 1‖ / ‖z - 1‖ := by
      have hden_nonneg : (0 : ℝ) ≤ ‖z - 1‖ := le_of_lt hden_pos
      exact div_le_div_of_nonneg_right hnum_ge hden_nonneg
    -- (phi^8-1)/(phi+1) ≤ (phi^8-1)/‖z-1‖ since ‖z-1‖ ≤ phi+1
    have h2 : (phi ^ 8 - 1) / (phi + 1) ≤ (phi ^ 8 - 1) / ‖z - 1‖ := by
      have hnum_nonneg : (0 : ℝ) ≤ phi ^ 8 - 1 := by
        have hgt : (1 : ℝ) < phi ^ 8 := one_lt_pow₀ one_lt_phi (by norm_num)
        linarith
      -- use `div_le_div_of_nonneg_left`
      have hphi1_pos : (0 : ℝ) < phi + 1 := by linarith [phi_pos]
      exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
    exact le_trans h2 h1

  -- Convert to a lower bound on the coefficient norm
  have hsqrt8_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt8_nonneg : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt hsqrt8_pos

  have hnorm_div : ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / Real.sqrt 8 := by
    have hsqrt8_nonneg' : (0 : ℝ) ≤ Real.sqrt 8 := hsqrt8_nonneg
    calc
      ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / ‖(Real.sqrt 8 : ℂ)‖ := by
        simpa using (norm_div S (Real.sqrt 8 : ℂ))
      _ = ‖S‖ / |Real.sqrt 8| := by
        simpa [RCLike.norm_ofReal] using
          congrArg (fun x : ℝ => ‖S‖ / x) (RCLike.norm_ofReal (K := ℂ) (Real.sqrt 8))
      _ = ‖S‖ / Real.sqrt 8 := by
        simp [abs_of_nonneg hsqrt8_nonneg']

  -- Lower bound on ‖S/√8‖
  have hcoeff_norm_ge : (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) ≤ ‖S / (Real.sqrt 8 : ℂ)‖ := by
    -- divide hS_ge by √8
    have hdiv : (phi ^ 8 - 1) / (phi + 1) / Real.sqrt 8 ≤ ‖S‖ / Real.sqrt 8 :=
      div_le_div_of_nonneg_right hS_ge hsqrt8_nonneg
    -- rewrite
    rw [hnorm_div]
    simpa [div_div, mul_assoc, mul_left_comm, mul_comm] using hdiv

  -- Now compare to a concrete numeric lower bound using phi bounds
  have hphi8_gt : (46.97 : ℝ) < phi ^ 8 := by
    have h : (46.97 : ℝ) < Real.goldenRatio ^ 8 := Numerics.phi_pow8_gt
    simpa [IndisputableMonolith.Constants.phi] using h
  have hphi1_lt : phi + 1 < (2.62 : ℝ) := by
    have hφ_lt : phi < (1.62 : ℝ) := phi_lt_onePointSixTwo
    linarith

  have hnum_gt : (45.97 : ℝ) < phi ^ 8 - 1 := by
    linarith [hphi8_gt]

  have hden_lt : (phi + 1) * Real.sqrt 8 < (2.62 : ℝ) * Real.sqrt 8 :=
    mul_lt_mul_of_pos_right hphi1_lt hsqrt8_pos

  have hden_posA : (0 : ℝ) < (2.62 : ℝ) * Real.sqrt 8 := by
    have : (0 : ℝ) < (2.62 : ℝ) := by norm_num
    exact mul_pos this hsqrt8_pos

  have hnum_pos : (0 : ℝ) < phi ^ 8 - 1 := by
    have hgt : (1 : ℝ) < phi ^ 8 := one_lt_pow₀ one_lt_phi (by norm_num)
    linarith

  -- first: 45.97 / (2.62*√8) < (phi^8-1) / (2.62*√8)
  have hstep1 : (45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8) < (phi ^ 8 - 1) / ((2.62 : ℝ) * Real.sqrt 8) :=
    div_lt_div_of_pos_right hnum_gt hden_posA

  -- second: (phi^8-1)/(2.62*√8) < (phi^8-1)/((phi+1)*√8)
  have hstep2 : (phi ^ 8 - 1) / ((2.62 : ℝ) * Real.sqrt 8) < (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) := by
    -- denominator decreases
    exact div_lt_div_of_pos_left hnum_pos (mul_pos (by linarith [phi_pos]) hsqrt8_pos) hden_lt

  have hfrac_lt : (45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8) < (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) :=
    lt_trans hstep1 hstep2

  -- square the inequality
  have hfrac_sq_lt : ((45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8))^2 < ((phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8))^2 := by
    have h0 : (0 : ℝ) ≤ (45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8) :=
      div_nonneg (by norm_num) (le_of_lt hden_posA)
    exact pow_lt_pow_left₀ hfrac_lt h0 (n := 2) (by decide : (2:ℕ) ≠ 0)

  -- show the constant square exceeds 38 by eliminating the sqrt
  have hconst_sq : (38 : ℝ) < ((45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8))^2 := by
    -- rewrite: (a/(b*sqrt8))^2 = a^2/(b^2*8)
    have hsqrt8_sq : (Real.sqrt 8)^2 = (8 : ℝ) := by
      -- `Real.sq_sqrt`
      simpa using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8))
    -- turn division into multiplication by inv and expand the square
    -- use `div_pow` and `mul_pow`
    --
    -- `norm_num` can finish once sqrt disappears.
    --
    -- We just `simp` to eliminate `(Real.sqrt 8)^2`.
    --
    -- (Lean rewriting)
    have : ((45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8))^2 = (45.97^2) / ((2.62^2) * 8) := by
      -- (a/(b*c))^2 = a^2 / ((b^2)*(c^2))
      -- we do it via `div_pow` twice.
      -- a/(b*c) = a / (b*c)
      rw [div_pow]
      -- denominator square
      rw [mul_pow]
      -- simplify (sqrt8)^2
      simp [pow_two, hsqrt8_sq]
    -- now reduce to rational inequality
    -- 38 < 45.97^2/(2.62^2*8)
    -- note: rewrite goal using `this`
    --
    -- `norm_num` can solve it.
    --
    --
    simpa [this] using (by
      norm_num : (38 : ℝ) < (45.97^2) / ((2.62^2) * 8))

  -- combine: 38 < const_sq < (phi^8-1)/(...)^2 <= ‖S/√8‖^2
  have hL_gt : (38 : ℝ) < ((phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8))^2 :=
    lt_trans hconst_sq hfrac_sq_lt

  have hL_le : ((phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8))^2 ≤ (‖S / (Real.sqrt 8 : ℂ)‖)^2 := by
    have h_nonneg : (0 : ℝ) ≤ (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) := by
      have hnum_nonneg : (0 : ℝ) ≤ phi ^ 8 - 1 := by
        have hgt : (1 : ℝ) < phi ^ 8 := one_lt_pow₀ one_lt_phi (by norm_num)
        linarith
      have hden_pos : (0 : ℝ) < (phi + 1) * Real.sqrt 8 := by
        have : (0 : ℝ) < phi + 1 := by linarith [phi_pos]
        exact mul_pos this hsqrt8_pos
      exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
    exact pow_le_pow_left₀ h_nonneg hcoeff_norm_ge 2

  have hgoal : (38 : ℝ) < (‖S / (Real.sqrt 8 : ℂ)‖)^2 :=
    lt_of_lt_of_le hL_gt hL_le

  -- finally, unfold the amplitude and finish
  unfold phiDFTAmplitude
  -- `normSq` is norm^2
  -- Use h_coeff to rewrite the coefficient.
  -- The simp-normal form uses `‖S‖^2 / 8`, so rewrite `hgoal` into that form.
  have hsqrt8_nonneg : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt hsqrt8_pos
  have habs : |Real.sqrt 8| = Real.sqrt 8 := abs_of_nonneg hsqrt8_nonneg
  have hsq : (Real.sqrt 8)^2 = (8 : ℝ) := by
    simpa using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8))
  have hrewrite : ((‖S‖ / |Real.sqrt 8|) ^ 2 : ℝ) = (‖S‖ ^ 2) / 8 := by
    rw [div_pow]
    simp [habs, hsq, pow_two]
  -- simplify the goal to the `/8` form
  simp [h_coeff, Complex.normSq_eq_norm_sq, hnorm_div, habs] at *
  -- after simp, `hgoal` is about `‖S‖ / |√8|`; transport it to `/8` using `hrewrite`
  have hgoal' : (38 : ℝ) < (‖S‖ ^ 2) / 8 := by
    -- `hgoal` currently: 38 < (‖S‖ / |√8|)^2
    -- rewrite RHS
    simpa [hrewrite] using hgoal
  exact hgoal'

end IndisputableMonolith.Constants.GapWeight
