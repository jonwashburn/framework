import Mathlib
import IndisputableMonolith.Constants.GapWeight
import IndisputableMonolith.Constants.GapWeight.Formula
import IndisputableMonolith.Numerics.Interval.PhiBounds

/-!
# Gap Weight Candidate Mismatch (Formal Refutation)

This module **refutes** the equation:

`GapWeight.w8_dft_candidate = Constants.w8_from_eight_tick`.

Why?
`w8_dft_candidate` is currently defined as the **raw** weighted DFT energy sum
\(\sum_{k\neq 0} |c_k|^2 g_k\).
The α-pipeline constant `w8_from_eight_tick` is a **normalized** quantity (and is
currently treated as an external computational certificate).

The proof here is intentionally conservative:
- We lower-bound a single term (k=1) of the candidate sum by a value \(> 2.5\).
- We upper-bound the certified constant by \(< 2.5\).
- Hence they cannot be equal.

This closes the “are they equal?” question: **no, not as currently defined**.
-/

namespace IndisputableMonolith
namespace Verification
namespace GapWeightCandidateMismatch

open scoped BigOperators

open IndisputableMonolith.Constants
open IndisputableMonolith.Constants.GapWeight
open IndisputableMonolith.LightLanguage.Basis
open IndisputableMonolith.Numerics
open Complex

/-! ## Trig / φ bounds used in the inequality -/

lemma sin_sq_pi_div_eight_gt_one_eighth : (1/8 : ℝ) < (Real.sin (Real.pi/8))^2 := by
  have hs : Real.sqrt 2 < (3/2 : ℝ) := Real.sqrt_two_lt_three_halves
  have h : (1/8 : ℝ) < (2 - Real.sqrt 2) / 4 := by
    nlinarith [hs]
  have hnonneg : 0 ≤ (2 - Real.sqrt 2) := by
    nlinarith [hs]
  have hsin_sq : (Real.sin (Real.pi/8))^2 = (2 - Real.sqrt 2) / 4 := by
    rw [Real.sin_pi_div_eight]
    rw [div_pow]
    rw [Real.sq_sqrt hnonneg]
    norm_num
  simpa [hsin_sq.symm] using h

lemma geometricWeight_one_gt_007725 : (0.07725 : ℝ) < geometricWeight (1 : Fin 8) := by
  have hk : (1 : Fin 8).val ≠ 0 := by decide
  have hsin : (1/8 : ℝ) < (Real.sin (Real.pi/8))^2 := sin_sq_pi_div_eight_gt_one_eighth
  have hphi : (0.618 : ℝ) < phi⁻¹ := by
    have h : (0.618 : ℝ) < Real.goldenRatio⁻¹ := Numerics.phi_inv_gt
    simpa [IndisputableMonolith.Constants.phi] using h
  have hconst : (0.07725 : ℝ) = (1/8 : ℝ) * (0.618 : ℝ) := by norm_num
  unfold geometricWeight
  simp [hk]
  have hpow : (phi : ℝ) ^ (-(1 : ℤ)) = phi⁻¹ := by
    simpa using (zpow_neg_one (phi : ℝ))
  have hprod : (1/8 : ℝ) * (0.618 : ℝ) < (Real.sin (Real.pi/8))^2 * (phi : ℝ) ^ (-(1 : ℤ)) := by
    have h0 : (0 : ℝ) ≤ (1/8 : ℝ) := by norm_num
    have h1 : (0 : ℝ) ≤ (0.618 : ℝ) := by norm_num
    have hphi' : (0.618 : ℝ) < (phi : ℝ) ^ (-(1 : ℤ)) := by
      simpa [hpow] using hphi
    exact mul_lt_mul'' hsin hphi' h0 h1
  simpa [hconst] using hprod

/-! ## DFT amplitude lower bound (k=1) -/

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

lemma phiDFTAmplitude_one_gt_38 : (38 : ℝ) < phiDFTAmplitude (1 : Fin 8) := by
  let z : ℂ := omega8 ^ 7 * (phi : ℂ)
  let S : ℂ := ∑ t : Fin 8, z ^ t.val

  have h_coeff : phiDFTCoeff (1 : Fin 8) = S / (Real.sqrt 8 : ℂ) := by
    unfold phiDFTCoeff dft8_entry phiPatternComplex phiPattern
    rw [Finset.sum_div]
    simp [S, z, dft8_entry, phiPatternComplex, phiPattern, star_div₀, star_pow, star_omega8,
      omega8_inv_eq_pow7, Nat.mul_one, mul_pow]
    simp [div_mul_eq_mul_div, mul_div, mul_assoc, mul_left_comm, mul_comm]

  have h_sum_geom : S * (z - 1) = z ^ 8 - 1 := by
    have h8 : S = z^0 + z^1 + z^2 + z^3 + z^4 + z^5 + z^6 + z^7 := by
      simp [S, Fin.sum_univ_eight]
    rw [h8]
    ring

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

  have hS_ge : (phi ^ 8 - 1) / (phi + 1) ≤ ‖S‖ := by
    have hS_eq : ‖S‖ = ‖z ^ 8 - 1‖ / ‖z - 1‖ := by
      have hden_ne : ‖z - 1‖ ≠ 0 := ne_of_gt hden_pos
      exact (eq_div_iff hden_ne).2 (by simpa [mul_comm] using hnorm)
    rw [hS_eq]
    have h1 : (phi ^ 8 - 1) / ‖z - 1‖ ≤ ‖z ^ 8 - 1‖ / ‖z - 1‖ := by
      have hden_nonneg : (0 : ℝ) ≤ ‖z - 1‖ := le_of_lt hden_pos
      exact div_le_div_of_nonneg_right hnum_ge hden_nonneg
    have h2 : (phi ^ 8 - 1) / (phi + 1) ≤ (phi ^ 8 - 1) / ‖z - 1‖ := by
      have hnum_nonneg : (0 : ℝ) ≤ phi ^ 8 - 1 := by
        have hgt : (1 : ℝ) < phi ^ 8 := one_lt_pow₀ one_lt_phi (by norm_num)
        linarith
      exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
    exact le_trans h2 h1

  have hsqrt8_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt8_nonneg : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt hsqrt8_pos

  have hcoeff_norm_ge : (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) ≤ ‖S / (Real.sqrt 8 : ℂ)‖ := by
    have hnorm_div : ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / Real.sqrt 8 := by
      calc
        ‖S / (Real.sqrt 8 : ℂ)‖ = ‖S‖ / ‖(Real.sqrt 8 : ℂ)‖ := by
          simpa using (norm_div S (Real.sqrt 8 : ℂ))
        _ = ‖S‖ / |Real.sqrt 8| := by
          simpa [RCLike.norm_ofReal] using
            congrArg (fun x : ℝ => ‖S‖ / x) (RCLike.norm_ofReal (K := ℂ) (Real.sqrt 8))
        _ = ‖S‖ / Real.sqrt 8 := by
          simp [abs_of_nonneg hsqrt8_nonneg]
    have hdiv : (phi ^ 8 - 1) / (phi + 1) / Real.sqrt 8 ≤ ‖S‖ / Real.sqrt 8 :=
      div_le_div_of_nonneg_right hS_ge hsqrt8_nonneg
    rw [hnorm_div]
    simpa [div_div, mul_assoc, mul_left_comm, mul_comm] using hdiv

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

  have hstep1 :
      (45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8) <
        (phi ^ 8 - 1) / ((2.62 : ℝ) * Real.sqrt 8) :=
    div_lt_div_of_pos_right hnum_gt hden_posA

  have hstep2 :
      (phi ^ 8 - 1) / ((2.62 : ℝ) * Real.sqrt 8) <
        (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) := by
    exact div_lt_div_of_pos_left hnum_pos (mul_pos (by linarith [phi_pos]) hsqrt8_pos) hden_lt

  have hfrac_lt :
      (45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8) <
        (phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8) :=
    lt_trans hstep1 hstep2

  have hfrac_sq_lt :
      ((45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8))^2 <
        ((phi ^ 8 - 1) / ((phi + 1) * Real.sqrt 8))^2 := by
    have h0 : (0 : ℝ) ≤ (45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8) :=
      div_nonneg (by norm_num) (le_of_lt hden_posA)
    exact pow_lt_pow_left₀ hfrac_lt h0 (n := 2) (by decide : (2:ℕ) ≠ 0)

  have hconst_sq : (38 : ℝ) < ((45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8))^2 := by
    have hsq : (Real.sqrt 8)^2 = (8 : ℝ) := by
      simpa using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8))
    have : ((45.97 : ℝ) / ((2.62 : ℝ) * Real.sqrt 8))^2 = (45.97^2) / ((2.62^2) * 8) := by
      rw [div_pow]
      rw [mul_pow]
      simp [pow_two, hsq]
    simpa [this] using (by
      norm_num : (38 : ℝ) < (45.97^2) / ((2.62^2) * 8))

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

  -- now translate to the actual DFT amplitude
  unfold phiDFTAmplitude
  -- simp-normal form uses `‖S‖^2 / 8`; rewrite `hgoal` accordingly.
  have hsqrt8_nonneg' : (0 : ℝ) ≤ Real.sqrt 8 := le_of_lt hsqrt8_pos
  have habs : |Real.sqrt 8| = Real.sqrt 8 := abs_of_nonneg hsqrt8_nonneg'
  have hsq' : (Real.sqrt 8)^2 = (8 : ℝ) := by
    simpa using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8))
  have hrewrite : ((‖S‖ / |Real.sqrt 8|) ^ 2 : ℝ) = (‖S‖ ^ 2) / 8 := by
    rw [div_pow]
    simp [habs, hsq', pow_two]
  simp [h_coeff, Complex.normSq_eq_norm_sq, habs] at *
  have hgoal' : (38 : ℝ) < (‖S‖ ^ 2) / 8 := by
    simpa [hrewrite] using hgoal
  exact hgoal'

/-! ## Final theorem: inequality, hence refutation -/

theorem w8_dft_candidate_ne_w8_from_eight_tick :
    w8_dft_candidate ≠ IndisputableMonolith.Constants.w8_from_eight_tick := by
  have h_term_le : phiDFTAmplitude (1 : Fin 8) * geometricWeight (1 : Fin 8) ≤ w8_dft_candidate := by
    unfold w8_dft_candidate
    have h_mem : (1 : Fin 8) ∈ Finset.filter (fun k : Fin 8 => k ≠ 0) Finset.univ := by decide
    have h_nonneg :
        ∀ k ∈ Finset.filter (fun k : Fin 8 => k ≠ 0) Finset.univ,
          0 ≤ phiDFTAmplitude k * geometricWeight k := by
      intro k hk
      exact mul_nonneg (phiDFTAmplitude_nonneg k) (geometricWeight_nonneg k)
    simpa using (Finset.single_le_sum (s := Finset.filter (fun k : Fin 8 => k ≠ 0) Finset.univ)
      (f := fun k : Fin 8 => phiDFTAmplitude k * geometricWeight k) h_nonneg h_mem)

  have hamp : (38 : ℝ) < phiDFTAmplitude (1 : Fin 8) := phiDFTAmplitude_one_gt_38
  have hgw : (0.07725 : ℝ) < geometricWeight (1 : Fin 8) := geometricWeight_one_gt_007725

  have hterm_gt : (2.5 : ℝ) < phiDFTAmplitude (1 : Fin 8) * geometricWeight (1 : Fin 8) := by
    have hbase : (2.5 : ℝ) < (38 : ℝ) * (0.07725 : ℝ) := by norm_num
    have h0 : (0 : ℝ) ≤ (38 : ℝ) := by norm_num
    have h1 : (0 : ℝ) ≤ (0.07725 : ℝ) := by norm_num
    have hlt : (38 : ℝ) * (0.07725 : ℝ) < phiDFTAmplitude (1 : Fin 8) * geometricWeight (1 : Fin 8) :=
      mul_lt_mul'' hamp hgw h0 h1
    exact lt_trans hbase hlt

  have hcand_gt : (2.5 : ℝ) < w8_dft_candidate := lt_of_lt_of_le hterm_gt h_term_le
  have hw8_lt : IndisputableMonolith.Constants.w8_from_eight_tick < (2.5 : ℝ) := by
    norm_num [IndisputableMonolith.Constants.w8_from_eight_tick]
  exact ne_of_gt (lt_trans hw8_lt hcand_gt)

end GapWeightCandidateMismatch
end Verification
end IndisputableMonolith
