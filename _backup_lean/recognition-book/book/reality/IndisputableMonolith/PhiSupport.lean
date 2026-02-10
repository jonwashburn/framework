import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace PhiSupport

/-- φ^2 = φ + 1 using the closed form φ = (1+√5)/2. -/
@[simp] theorem phi_squared : Constants.phi ^ 2 = Constants.phi + 1 := by
  -- Expand ((1+√5)/2)^2
  have hdef : Constants.phi = (1 + Real.sqrt 5) / 2 := rfl
  have : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2
       = ((1 + Real.sqrt 5) ^ 2) / 4 := by
    ring
  have hsq : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
    have : (1 + Real.sqrt 5) ^ 2 = 1 + 2 * Real.sqrt 5 + (Real.sqrt 5) ^ 2 := by ring
    have : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
      have : 0 ≤ (5 : ℝ) := by norm_num
      simpa [pow_two] using Real.sqrt_mul_self this
    simpa [this] using by
      have : 1 + 2 * Real.sqrt 5 + 5 = 6 + 2 * Real.sqrt 5 := by ring
      simpa [this]
  have hsq_div : ((1 + Real.sqrt 5) / 2 : ℝ) ^ 2 = (6 + 2 * Real.sqrt 5) / 4 := by
    simpa [this] using hsq
  -- Also φ + 1 = ((1+√5)+2)/2
  have hplus : (1 + Real.sqrt 5) / 2 + 1 = (3 + Real.sqrt 5) / 2 := by
    ring
  -- Put everything together
  simpa [hdef, hsq_div, hplus, two_mul, add_comm, add_left_comm, add_assoc] using by
    ring

/-- φ = 1 + 1/φ as a direct algebraic corollary of φ^2 = φ + 1 and φ ≠ 0. -/
@[simp] theorem phi_fixed_point : Constants.phi = 1 + 1 / Constants.phi := by
  have hsq : Constants.phi ^ 2 = Constants.phi + 1 := phi_squared
  have hpos : 0 < Constants.phi := IndisputableMonolith.Constants.phi_pos
  have hne : Constants.phi ≠ 0 := ne_of_gt hpos
  have := congrArg (fun x => x / Constants.phi) hsq
  -- Simplify both sides after dividing by φ
  -- (φ^2)/φ = φ and (φ+1)/φ = 1 + 1/φ
  have : Constants.phi = 1 + 1 / Constants.phi := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
  simpa [add_comm, add_left_comm, add_assoc] using this

/-! Uniqueness: the positive real solution to x² = x + 1 is φ. -/

theorem phi_unique_pos_root : ∀ x : ℝ, (x ^ 2 = x + 1 ∧ 0 < x) ↔ x = Constants.phi := by
  intro x
  constructor
  · intro hx
    have hx_sq := hx.1
    have hx_pos := hx.2
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    -- Turn quadratic into fixed point: x = 1 + 1/x
    have hx_fp : x = 1 + 1 / x := by
      have := congrArg (fun t => t / x) hx_sq
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, hx_ne] using this
    -- Compare with φ’s fixed point; define g(t)=t−1−1/t, strictly increasing on (0,∞)
    have gφ : Constants.phi - 1 - 1 / Constants.phi = 0 := by
      have := phi_fixed_point
      have := sub_eq_zero_of_eq this
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have gx : x - 1 - 1 / x = 0 := by
      have := hx_fp
      have := sub_eq_zero_of_eq this
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have φ_pos : 0 < Constants.phi := IndisputableMonolith.Constants.phi_pos
    -- If x ≠ φ, then either x < φ or φ < x; strict monotonicity of g contradicts gx=gφ=0.
    by_contra hneq
    have hlt_or_gt : x < Constants.phi ∨ Constants.phi < x := lt_or_gt_of_ne hneq
    have strict_mono_g : ∀ {a b}, 0 < a → a < b → (b - 1 - 1 / b) > (a - 1 - 1 / a) := by
      intro a b ha_pos hlt
      have hb_pos : 0 < b := lt_trans ha_pos hlt
      have hrec : 1 / b < 1 / a := by
        -- inv_lt_inv_of_lt: 0 < a → a < b → b⁻¹ < a⁻¹
        have := inv_lt_inv_of_lt ha_pos hlt
        simpa [one_div] using this
      have h1 : 0 < b - a := sub_pos.mpr hlt
      have h2 : 0 < 1 / a - 1 / b := sub_pos.mpr hrec
      have : 0 < (b - a) + (1 / a - 1 / b) := add_pos h1 h2
      -- g(b) - g(a) = (b-a) + (1/a - 1/b)
      have : (b - 1 - 1 / b) - (a - 1 - 1 / a) > 0 := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      -- rearrange to g(b) > g(a)
      simpa [sub_eq, sub_eq_add_neg] using this
    rcases hlt_or_gt with hlt | hgt
    · have : (Constants.phi - 1 - 1 / Constants.phi) > (x - 1 - 1 / x) :=
        strict_mono_g (by exact hx_pos) hlt
      have : 0 > 0 := by simpa [gφ, gx] using this
      exact lt_irrefl _ this
    · have : (x - 1 - 1 / x) > (Constants.phi - 1 - 1 / Constants.phi) :=
        strict_mono_g (by exact φ_pos) hgt
      have : 0 > 0 := by simpa [gφ, gx] using this
      exact lt_irrefl _ this
    -- contradiction, hence x = φ
  · intro hx
    refine And.intro ?hEq ?hPos
    · simpa [hx] using phi_squared
    · have : 1 < Constants.phi := IndisputableMonolith.Constants.one_lt_phi
      exact lt_trans (by norm_num) this

end PhiSupport
end IndisputableMonolith
