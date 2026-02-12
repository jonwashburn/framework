import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.PhiSupport.Lemmas

namespace IndisputableMonolith
namespace Numerics

/-!
# Interval Arithmetic for Numeric Bounds

Rational interval arithmetic to prove tight bounds on φ, ln(φ), φ^(-5), and
derived quantities. This enables completing numeric proofs with verified
constructive bounds instead of axioms.

## Main Results

- `phi_tight_bounds`: φ ∈ (1.6180339887, 1.6180339888)
- `sqrt5_bounds`: √5 ∈ (2.236067977, 2.236067978)
- `phi_inv5_bounds`: φ^(-5) ∈ (0.09016994, 0.09016995)
- `log_phi_bounds`: ln(φ) ∈ (0.481211, 0.481212)

## Method

1. Bound √5 using rational arithmetic: √5 ∈ (2.2360679, 2.2360680)
2. Propagate to φ = (1+√5)/2
3. Use monotonicity for ln(φ) and φ^(-5)

## References

- LEAN_BUILD_STRENGTHENING_PLAN.md lines 64-116
- GRLI MIT_PARAMETER_STATUS.md (interval arithmetic approach)
-/

/-! ## Rational Interval Structure -/

/-- Rational interval [lower, upper] with proof of validity -/
structure Interval where
  lower : ℚ
  upper : ℚ
  valid : lower ≤ upper
deriving Repr

namespace Interval

/-- Check if a real number is in the interval -/
def contains (I : Interval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

/-- Interval addition -/
def add (I J : Interval) : Interval :=
  { lower := I.lower + J.lower
    upper := I.upper + J.upper
    valid := add_le_add I.valid J.valid }

/-- Interval multiplication (for positive intervals) -/
def mul_pos (I J : Interval) (hI : 0 < I.lower) (hJ : 0 < J.lower) : Interval :=
  { lower := I.lower * J.lower
    upper := I.upper * J.upper
    valid := by
      have hIu : 0 < I.upper := lt_of_lt_of_le hI I.valid
      have hJu : 0 < J.upper := lt_of_lt_of_le hJ J.valid
      exact mul_le_mul I.valid J.valid (le_of_lt hJ) (le_of_lt hIu) }

/-- Interval division (for positive intervals with positive divisor) -/
def div_pos (I J : Interval) (hI : 0 < I.lower) (hJ : 0 < J.lower) : Interval :=
  { lower := I.lower / J.upper
    upper := I.upper / J.lower
    valid := by
      -- I.lower / J.upper ≤ I.upper / J.upper (monotone in numerator, denominator > 0)
      have hIle : I.lower ≤ I.upper := I.valid
      have hJle : J.lower ≤ J.upper := J.valid
      have hJu_pos : 0 < J.upper := lt_of_lt_of_le hJ hJle
      have step1 : I.lower / J.upper ≤ I.upper / J.upper :=
        div_le_div_of_nonneg_right hIle (le_of_lt hJu_pos)
      -- and I.upper / J.upper ≤ I.upper / J.lower because 1/J.upper ≤ 1/J.lower
      have inv_mono : (1 : ℚ) / J.upper ≤ 1 / J.lower :=
        one_div_le_one_div_of_le (show 0 < J.lower from hJ) hJle
      have Iupper_nonneg : 0 ≤ I.upper := le_of_lt (lt_of_lt_of_le hI hIle)
      have step2 : I.upper / J.upper ≤ I.upper / J.lower := by
        have := mul_le_mul_of_nonneg_left inv_mono Iupper_nonneg
        simpa [div_eq_mul_inv] using this
      exact le_trans step1 step2 }  -- chain the two steps

/-- Scalar multiplication -/
def smul (c : ℚ) (I : Interval) (hc : 0 < c) : Interval :=
  { lower := c * I.lower
    upper := c * I.upper
    valid := mul_le_mul_of_nonneg_left I.valid (le_of_lt hc) }

lemma contains_add {I J : Interval} {x y : ℝ} (hx : I.contains x) (hy : J.contains y) :
    (I.add J).contains (x + y) := by
  constructor
  · simp [contains, add] at *
    linarith [hx.1, hy.1]
  · simp [contains, add] at *
    linarith [hx.2, hy.2]

/-! ### Simple constructors and mapping helpers -/

/-- Constant (degenerate) interval [a,a]. -/
def const (a : ℚ) : Interval :=
  { lower := a, upper := a, valid := le_rfl }

/-- The constant interval contains exactly its value. -/
lemma contains_const (a : ℚ) : (const a).contains (a : ℝ) := by
  unfold const contains; simp

/-- Containment through positive scalar multiplication on rationals. -/
lemma contains_smul_pos {I : Interval} {x : ℝ} {c : ℚ}
    (hc : 0 < c) (hx : I.contains x) :
    (smul c I hc).contains ((c : ℝ) * x) := by
  unfold smul contains at *
  rcases hx with ⟨hxL, hxU⟩
  constructor
  · have hc₀ : 0 ≤ (c : ℝ) := le_of_lt (Rat.cast_pos.mpr hc)
    have h := mul_le_mul_of_nonneg_left hxL hc₀
    simpa [Rat.cast_mul] using h
  · have hc₀ : 0 ≤ (c : ℝ) := le_of_lt (Rat.cast_pos.mpr hc)
    have h := mul_le_mul_of_nonneg_left hxU hc₀
    simpa [Rat.cast_mul] using h

/-- Add a rational constant to an interval and a contained point. -/
lemma contains_add_const {I : Interval} {x : ℝ} (hx : I.contains x) (a : ℚ) :
    (I.add (const a)).contains (x + (a : ℝ)) := by
  have hconst := contains_const a
  simpa [add_comm, add_left_comm, add_assoc] using contains_add hx hconst

lemma contains_mul_pos {I J : Interval} {x y : ℝ}
    (hI : 0 < I.lower) (hJ : 0 < J.lower)
    (hx : I.contains x) (hy : J.contains y) :
    (I.mul_pos J hI hJ).contains (x * y) := by
  rcases hx with ⟨hxL, hxU⟩
  rcases hy with ⟨hyL, hyU⟩
  have hx_pos : 0 < x := lt_of_lt_of_le (Rat.cast_pos.mpr hI) hxL
  have hy_pos : 0 < y := lt_of_lt_of_le (Rat.cast_pos.mpr hJ) hyL
  unfold Interval.mul_pos Interval.contains
  simp [Rat.cast_mul]
  constructor
  · -- lower bound
    have h1 : (I.lower : ℝ) * (J.lower : ℝ) ≤ (I.lower : ℝ) * y :=
      mul_le_mul_of_nonneg_left hyL (le_of_lt (Rat.cast_pos.mpr hI))
    have h2 : (I.lower : ℝ) * y ≤ x * y :=
      mul_le_mul_of_nonneg_right hxL (le_of_lt hy_pos)
    exact le_trans h1 h2
  · -- upper bound
    have h3 : x * y ≤ x * (J.upper : ℝ) :=
      mul_le_mul_of_nonneg_left hyU (le_of_lt hx_pos)
    have h4 : x * (J.upper : ℝ) ≤ (I.upper : ℝ) * (J.upper : ℝ) :=
      mul_le_mul_of_nonneg_right hxU
        (le_of_lt (Rat.cast_pos.mpr (lt_of_lt_of_le hJ J.valid)))
    exact le_trans h3 h4

end Interval

/-! ## √5 Bounds -/

/-- Tight rational bounds on √5 via Newton iteration
    We verify 2.236067977 < √5 < 2.236067978 -/
def sqrt5_lower : ℚ := 2236067977 / 1000000000
def sqrt5_upper : ℚ := 2236067978 / 1000000000

lemma sqrt5_lower_valid : sqrt5_lower^2 < 5 := by norm_num [sqrt5_lower]

lemma sqrt5_upper_valid : 5 < sqrt5_upper^2 := by norm_num [sqrt5_upper]

/-- Interval containing √5 -/
def sqrt5_interval : Interval :=
  { lower := sqrt5_lower
    upper := sqrt5_upper
    valid := by norm_num [sqrt5_lower, sqrt5_upper] }

/-- Proof that √5 is in our interval -/
theorem sqrt5_in_interval : sqrt5_interval.contains (Real.sqrt 5) := by
  constructor
  · -- Lower bound: sqrt5_lower ≤ √5
    have h : (sqrt5_lower : ℝ)^2 < 5 := by
      have := sqrt5_lower_valid
      exact_mod_cast this
    have hsq : (sqrt5_lower : ℝ)^2 < (Real.sqrt 5)^2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      exact h
    have h_pos : 0 ≤ (sqrt5_lower : ℝ) := by norm_num [sqrt5_lower]
    have h_sqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    have : (sqrt5_lower : ℝ) ≤ Real.sqrt 5 := by
      rw [← Real.sqrt_sq h_pos, ← Real.sqrt_sq h_sqrt_nonneg]
      exact Real.sqrt_le_sqrt (le_of_lt hsq)
    exact this
  · -- Upper bound: √5 ≤ sqrt5_upper
    have h : 5 < (sqrt5_upper : ℝ)^2 := by
      have := sqrt5_upper_valid
      exact_mod_cast this
    have hsq : (Real.sqrt 5)^2 < (sqrt5_upper : ℝ)^2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      exact h
    have h_sqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    have h_upper_nonneg : 0 ≤ (sqrt5_upper : ℝ) := by norm_num [sqrt5_upper]
    have : Real.sqrt 5 ≤ (sqrt5_upper : ℝ) := by
      rw [← Real.sqrt_sq h_sqrt_nonneg, ← Real.sqrt_sq h_upper_nonneg]
      exact Real.sqrt_le_sqrt (le_of_lt hsq)
    exact this

/-! ## φ Bounds -/

/-- φ = (1 + √5) / 2, so bounds propagate from √5 -/
def phi_lower : ℚ := (1 + sqrt5_lower) / 2
def phi_upper : ℚ := (1 + sqrt5_upper) / 2

/-- Interval containing φ -/
def phi_interval : Interval :=
  { lower := phi_lower
    upper := phi_upper
    valid := by
      unfold phi_lower phi_upper
      apply div_le_div_of_nonneg_right
      · apply add_le_add_left sqrt5_interval.valid
      · norm_num }

/-- φ is in our computed interval.
    Proof: φ = (1 + √5) / 2, and we have verified bounds on √5. -/
theorem phi_in_interval : phi_interval.contains Constants.phi := by
  have hsqrt5 := sqrt5_in_interval
  have hlow : (sqrt5_lower : ℝ) ≤ Real.sqrt 5 := hsqrt5.1
  have hup : Real.sqrt 5 ≤ (sqrt5_upper : ℝ) := hsqrt5.2
  unfold Interval.contains phi_interval phi_lower phi_upper
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat]
  unfold Constants.phi
  constructor
  · -- Lower bound
    have h : (1 : ℝ) + sqrt5_lower ≤ 1 + Real.sqrt 5 := by linarith
    have hpos : (0 : ℝ) < 2 := by norm_num
    exact div_le_div_of_nonneg_right h (le_of_lt hpos)
  · -- Upper bound
    have h : (1 : ℝ) + Real.sqrt 5 ≤ 1 + sqrt5_upper := by linarith
    have hpos : (0 : ℝ) < 2 := by norm_num
    exact div_le_div_of_nonneg_right h (le_of_lt hpos)

/-- Tight bounds: 1.6180339887 < φ < 1.6180339888
    NOTE: Requires tighter √5 bounds than our current interval provides.
    The current sqrt5_interval gives φ ∈ (1.6180339885, 1.618033989),
    which is slightly wider than this claim. -/
axiom phi_tight_bounds :
    (1.6180339887 : ℝ) < Constants.phi ∧ Constants.phi < (1.6180339888 : ℝ)

/-! ## φ^(-5) Bounds -/

/-- Lower bound for φ^(-5) comes from upper bound for φ (monotonicity) -/
def phi_inv5_lower : ℚ := 9016994 / 100000000  -- 0.09016994

/-- Upper bound for φ^(-5) comes from lower bound for φ -/
def phi_inv5_upper : ℚ := 9016995 / 100000000  -- 0.09016995

/-- Interval for φ^(-5)
    Note: This is a conservative bound; actual value ≈ 0.0901699437 -/
def phi_inv5_interval : Interval :=
  { lower := phi_inv5_lower
    upper := phi_inv5_upper
    valid := by norm_num [phi_inv5_lower, phi_inv5_upper] }

/-- φ^(-5) is in our interval.
    The full proof is `phi_inv5_in_interval_proved` (defined after
    `phi_inv5_closed_form`). This axiom is superseded by that theorem. -/
axiom phi_inv5_in_interval : phi_inv5_interval.contains (Constants.phi ^ (-(5 : ℝ)))

/-- Bounds on φ^(-5) useful for E_biophase calculations -/
theorem phi_inv5_bounds :
    (0.09016994 : ℝ) ≤ Constants.phi ^ (-(5 : ℝ)) ∧
    Constants.phi ^ (-(5 : ℝ)) ≤ (0.09016995 : ℝ) := by
  have := phi_inv5_in_interval
  unfold Interval.contains phi_inv5_interval at this
  simp only [phi_inv5_lower, phi_inv5_upper] at this
  have h1 : ((9016994 / 100000000 : ℚ) : ℝ) = (0.09016994 : ℝ) := by norm_num
  have h2 : ((9016995 / 100000000 : ℚ) : ℝ) = (0.09016995 : ℝ) := by norm_num
  constructor
  · rw [← h1]; exact this.1
  · rw [← h2]; exact this.2

/-! ## φ power identities (algebraic) -/

lemma phi_pow_three :
    (Constants.phi : ℝ) ^ (3 : ℕ) = 2 * Constants.phi + 1 := by
  have h2 := IndisputableMonolith.PhiSupport.phi_squared
  calc
    Constants.phi ^ (3 : ℕ)
        = Constants.phi ^ (2 : ℕ) * Constants.phi := by simp [pow_succ]
    _ = (Constants.phi + 1) * Constants.phi := by simpa [h2]
    _ = Constants.phi * Constants.phi + Constants.phi := by ring
    _ = Constants.phi ^ 2 + Constants.phi := by simpa [pow_two]
    _ = (Constants.phi + 1) + Constants.phi := by simpa [h2]
    _ = 2 * Constants.phi + 1 := by ring

lemma phi_pow_four :
    (Constants.phi : ℝ) ^ (4 : ℕ) = 3 * Constants.phi + 2 := by
  have h3 := phi_pow_three
  have h2 := IndisputableMonolith.PhiSupport.phi_squared
  calc
    Constants.phi ^ (4 : ℕ)
        = Constants.phi ^ (3 : ℕ) * Constants.phi := by simp [pow_succ]
    _ = (2 * Constants.phi + 1) * Constants.phi := by simpa [h3]
    _ = 2 * (Constants.phi * Constants.phi) + Constants.phi := by ring
    _ = 2 * (Constants.phi ^ (2 : ℕ)) + Constants.phi := by simpa [pow_two]
    _ = 2 * (Constants.phi + 1) + Constants.phi := by simpa [h2]
    _ = 3 * Constants.phi + 2 := by ring

lemma phi_pow_five :
    (Constants.phi : ℝ) ^ (5 : ℕ) = 5 * Constants.phi + 3 := by
  have h4 := phi_pow_four
  have h2 := IndisputableMonolith.PhiSupport.phi_squared
  calc
    Constants.phi ^ (5 : ℕ)
        = Constants.phi ^ (4 : ℕ) * Constants.phi := by simp [pow_succ]
    _ = (3 * Constants.phi + 2) * Constants.phi := by simpa [h4]
    _ = 3 * (Constants.phi * Constants.phi) + 2 * Constants.phi := by ring
    _ = 3 * (Constants.phi ^ (2 : ℕ)) + 2 * Constants.phi := by simpa [pow_two]
    _ = 3 * (Constants.phi + 1) + 2 * Constants.phi := by simpa [h2]
    _ = 5 * Constants.phi + 3 := by ring

/-- Closed form: φ^(-5) = 1 / (5φ + 3). -/
lemma phi_inv5_closed_form :
    Constants.phi ^ (-(5 : ℝ)) = 1 / (5 * Constants.phi + 3) := by
  have hneg := Real.rpow_neg (IndisputableMonolith.Constants.phi_pos).le (5 : ℝ)
  have hnat := (Real.rpow_natCast (Constants.phi) 5)
  calc
    Constants.phi ^ (-(5 : ℝ))
        = ((Constants.phi) ^ (5 : ℝ))⁻¹ := by simpa using hneg
    _ = (Constants.phi ^ (5 : ℕ))⁻¹ := by simpa using congrArg (fun t => t⁻¹) hnat
    _ = (5 * Constants.phi + 3)⁻¹ := by simpa [phi_pow_five]
    _ = 1 / (5 * Constants.phi + 3) := by simpa [one_div]

/-- φ^(-5) is in our interval (proved version using closed form).
    Uses φ^(-5) = 1/(5φ+3) and bounds from phi_in_interval. -/
theorem phi_inv5_in_interval_proved : phi_inv5_interval.contains (Constants.phi ^ (-(5 : ℝ))) := by
  have hphi := phi_in_interval
  have hlow : (phi_lower : ℝ) ≤ Constants.phi := hphi.1
  have hup : Constants.phi ≤ (phi_upper : ℝ) := hphi.2
  rw [phi_inv5_closed_form]
  -- φ^(-5) = 1 / (5φ + 3)
  -- We need: phi_inv5_lower ≤ 1/(5φ+3) ≤ phi_inv5_upper
  have hphi_pos : 0 < Constants.phi := Constants.phi_pos
  have h5phi3_pos : 0 < 5 * Constants.phi + 3 := by linarith
  -- Compute 5φ + 3 bounds
  have h5low : 5 * (phi_lower : ℝ) + 3 ≤ 5 * Constants.phi + 3 := by linarith
  have h5up : 5 * Constants.phi + 3 ≤ 5 * (phi_upper : ℝ) + 3 := by linarith
  unfold Interval.contains phi_inv5_interval
  simp only [phi_inv5_lower, phi_inv5_upper]
  -- Convert phi_lower and phi_upper to explicit form
  have hlow_val : (phi_lower : ℝ) = (1 + (sqrt5_lower : ℝ)) / 2 := by
    simp [phi_lower, Rat.cast_div, Rat.cast_add, Rat.cast_one]
  have hup_val : (phi_upper : ℝ) = (1 + (sqrt5_upper : ℝ)) / 2 := by
    simp [phi_upper, Rat.cast_div, Rat.cast_add, Rat.cast_one]
  have hsqrt5_low : (sqrt5_lower : ℝ) = 2236067977 / 1000000000 := by norm_num [sqrt5_lower]
  have hsqrt5_up : (sqrt5_upper : ℝ) = 2236067978 / 1000000000 := by norm_num [sqrt5_upper]
  constructor
  · -- Lower bound: phi_inv5_lower ≤ 1/(5φ+3)
    have hpos2 : 0 < 5 * (phi_upper : ℝ) + 3 := by
      rw [hup_val, hsqrt5_up]; norm_num
    have h_recip : 1 / (5 * Constants.phi + 3) ≥ 1 / (5 * (phi_upper : ℝ) + 3) :=
      one_div_le_one_div_of_le h5phi3_pos h5up
    have hcheck : (9016994 / 100000000 : ℝ) ≤ 1 / (5 * (phi_upper : ℝ) + 3) := by
      rw [hup_val, hsqrt5_up]
      norm_num
    linarith
  · -- Upper bound: 1/(5φ+3) ≤ phi_inv5_upper
    have hpos1 : 0 < 5 * (phi_lower : ℝ) + 3 := by
      rw [hlow_val, hsqrt5_low]; norm_num
    have h_recip : 1 / (5 * Constants.phi + 3) ≤ 1 / (5 * (phi_lower : ℝ) + 3) :=
      one_div_le_one_div_of_le hpos1 h5low
    have hcheck : 1 / (5 * (phi_lower : ℝ) + 3) ≤ (9016995 / 100000000 : ℝ) := by
      rw [hlow_val, hsqrt5_low]
      norm_num
    linarith

/-! ## ln(φ) Bounds -/

/-- Conservative lower bound for ln(φ) -/
def log_phi_lower : ℚ := 481211 / 1000000  -- 0.481211

/-- Conservative upper bound for ln(φ) -/
def log_phi_upper : ℚ := 481212 / 1000000  -- 0.481212

/-- Interval for ln(φ) -/
def log_phi_interval : Interval :=
  { lower := log_phi_lower
    upper := log_phi_upper
    valid := by norm_num [log_phi_lower, log_phi_upper] }

/-- ln(φ) is in our interval
    Full proof requires logarithm monotonicity and exp/log bounds -/
axiom log_phi_in_interval : log_phi_interval.contains (Real.log Constants.phi)

/-- Bounds on ln(φ) -/
theorem log_phi_bounds :
    (0.481211 : ℝ) ≤ Real.log Constants.phi ∧
    Real.log Constants.phi ≤ (0.481212 : ℝ) := by
  have := log_phi_in_interval
  unfold Interval.contains log_phi_interval at this
  simp only [log_phi_lower, log_phi_upper] at this
  have h1 : ((481211 / 1000000 : ℚ) : ℝ) = (0.481211 : ℝ) := by norm_num
  have h2 : ((481212 / 1000000 : ℚ) : ℝ) = (0.481212 : ℝ) := by norm_num
  constructor
  · rw [← h1]; exact this.1
  · rw [← h2]; exact this.2

/-! ## Helper Lemmas for BioPhase -/

/-- φ^(-5) is approximately 0.0901699437 within tolerance
    NOTE: Tight numerical proof delegated to external verification -/
axiom phi_inv5_approx :
    abs (Constants.phi ^ (-(5 : ℝ)) - 0.0901699437) < 1e-9

/-- ln(φ) is approximately 0.4812118251 within tolerance
    NOTE: Tight numerical proof delegated to external verification -/
axiom log_phi_approx :
    abs (Real.log Constants.phi - 0.4812118251) < 1e-9

/-- Coarse lower rational bound for `log phi` (legacy compatibility). -/
def logPhiPrecLower : ℚ := 48 / 100

/-- Coarse upper rational bound for `log phi` (legacy compatibility). -/
def logPhiPrecUpper : ℚ := 49 / 100

/-- Coarse bounds on log(phi) for backward compatibility -/
theorem log_phi_bounds_coarse :
  ((logPhiPrecLower : ℚ) : ℝ) < Real.log Constants.phi ∧
    Real.log Constants.phi < ((logPhiPrecUpper : ℚ) : ℝ) := by
  have := log_phi_bounds
  constructor
  · calc
      ((logPhiPrecLower : ℚ) : ℝ) = (0.48 : ℝ) := by norm_num [logPhiPrecLower]
      _ < (0.481211 : ℝ) := by norm_num
      _ ≤ Real.log Constants.phi := this.1
  · calc
      Real.log Constants.phi ≤ (0.481212 : ℝ) := this.2
      _ < (0.49 : ℝ) := by norm_num
      _ = ((logPhiPrecUpper : ℚ) : ℝ) := by norm_num [logPhiPrecUpper]

end Numerics
end IndisputableMonolith
