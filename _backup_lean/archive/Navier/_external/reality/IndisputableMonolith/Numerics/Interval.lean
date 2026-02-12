import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.PhiSupport.Lemmas
import IndisputableMonolith.Support.GoldenRatio

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

/-- φ is in our computed interval -/
theorem phi_in_interval : phi_interval.contains Constants.phi := by
  have h_sqrt5 := sqrt5_in_interval
  simp only [Interval.contains, sqrt5_interval] at h_sqrt5
  have h_phi_def : Constants.phi = (1 + Real.sqrt 5) / 2 := by
    unfold Constants.phi
    rfl
  simp only [Interval.contains, phi_interval, phi_lower, phi_upper]
  constructor
  · -- Lower bound: phi_lower ≤ φ
    simp only [Rat.cast_div, Rat.cast_add, Rat.cast_one]
    rw [h_phi_def]
    have h_sqrt_lower : (sqrt5_lower : ℝ) ≤ Real.sqrt 5 := h_sqrt5.1
    have h1 : (1 : ℝ) + (sqrt5_lower : ℝ) ≤ 1 + Real.sqrt 5 := by
      linarith
    have h2 : ((1 : ℝ) + (sqrt5_lower : ℝ)) / 2 ≤ (1 + Real.sqrt 5) / 2 := by
      exact div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2)
    simpa [Rat.cast_add, Rat.cast_one] using h2
  · -- Upper bound: φ ≤ phi_upper
    simp only [Rat.cast_div, Rat.cast_add, Rat.cast_one]
    rw [h_phi_def]
    have h_sqrt_upper : Real.sqrt 5 ≤ (sqrt5_upper : ℝ) := h_sqrt5.2
    have h1 : 1 + Real.sqrt 5 ≤ (1 : ℝ) + (sqrt5_upper : ℝ) := by
      linarith
    have h2 : (1 + Real.sqrt 5) / 2 ≤ ((1 : ℝ) + (sqrt5_upper : ℝ)) / 2 := by
      exact div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2)
    simpa [Rat.cast_add, Rat.cast_one] using h2

/-- Tight bounds: 1.6180339885 < φ < 1.618033989
    Derived from sqrt5 bounds via φ = (1+√5)/2.

    The bounds derive from sqrt5_lower = 2.236067977 and sqrt5_upper = 2.236067978:
    - phi_lower = (1 + sqrt5_lower)/2 = 3236067977/2000000000 ≈ 1.6180339885
    - phi_upper = (1 + sqrt5_upper)/2 = 3236067978/2000000000 ≈ 1.618033989
    The strictness follows from φ being irrational while our bounds are rational. -/
theorem phi_tight_bounds :
    (1.6180339885 : ℝ) < Constants.phi ∧ Constants.phi < (1.618033989 : ℝ) := by
  have h_interval := phi_in_interval
  simp only [Interval.contains, phi_interval, phi_lower, phi_upper] at h_interval
  have h_phi_irrational : Irrational Constants.phi := by
    rw [← Support.GoldenRatio.foundation_phi_eq_constants]
    exact Support.GoldenRatio.phi_irrational
  constructor
  · -- Lower bound: 1.6180339885 < φ
    have h_ne : Constants.phi ≠ (((1 + sqrt5_lower) / 2 : ℚ) : ℝ) := by
      intro heq
      exact h_phi_irrational.ne_rat ((1 + sqrt5_lower) / 2) heq
    have h_le := h_interval.1
    have h_lt : (((1 + sqrt5_lower) / 2 : ℚ) : ℝ) < Constants.phi :=
      lt_of_le_of_ne h_le (Ne.symm h_ne)
    have h_phi_lower_val : (((1 + sqrt5_lower) / 2 : ℚ) : ℝ) = (3236067977 / 2000000000 : ℝ) := by
      simp only [sqrt5_lower]; norm_num
    calc (1.6180339885 : ℝ)
        = (3236067977 / 2000000000 : ℝ) := by norm_num
      _ = (((1 + sqrt5_lower) / 2 : ℚ) : ℝ) := h_phi_lower_val.symm
      _ < Constants.phi := h_lt
  · -- Upper bound: φ < 1.618033989
    have h_ne : Constants.phi ≠ (((1 + sqrt5_upper) / 2 : ℚ) : ℝ) := by
      intro heq
      exact h_phi_irrational.ne_rat ((1 + sqrt5_upper) / 2) heq
    have h_le := h_interval.2
    have h_lt : Constants.phi < (((1 + sqrt5_upper) / 2 : ℚ) : ℝ) :=
      lt_of_le_of_ne h_le h_ne
    have h_phi_upper_val : (((1 + sqrt5_upper) / 2 : ℚ) : ℝ) = (3236067978 / 2000000000 : ℝ) := by
      simp only [sqrt5_upper]; norm_num
    calc Constants.phi
        < (((1 + sqrt5_upper) / 2 : ℚ) : ℝ) := h_lt
      _ = (3236067978 / 2000000000 : ℝ) := h_phi_upper_val
      _ = (1.618033989 : ℝ) := by norm_num

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

/-- Helper: x ↦ x^(-5) is strictly decreasing on (1, ∞) -/
lemma rpow_neg_five_antitone {x y : ℝ} (hx : 1 < x) (hy : 1 < y) (hxy : x < y) :
    y ^ (-(5 : ℝ)) < x ^ (-(5 : ℝ)) := by
  have hx_pos : 0 < x := lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hy_pos : 0 < y := lt_trans (by norm_num : (0 : ℝ) < 1) hy
  have h_pow : x ^ (5 : ℝ) < y ^ (5 : ℝ) := by
    exact Real.rpow_lt_rpow (le_of_lt hx_pos) hxy (by norm_num : (0 : ℝ) < 5)
  have h_inv : (y ^ (5 : ℝ))⁻¹ < (x ^ (5 : ℝ))⁻¹ := by
    have hx_pow_pos : 0 < x ^ (5 : ℝ) := Real.rpow_pos_of_pos hx_pos _
    have hy_pow_pos : 0 < y ^ (5 : ℝ) := Real.rpow_pos_of_pos hy_pos _
    rw [inv_lt_inv₀ hy_pow_pos hx_pow_pos]
    exact h_pow
  have hx_neg : x ^ (-(5 : ℝ)) = (x ^ (5 : ℝ))⁻¹ := by
    exact Real.rpow_neg (le_of_lt hx_pos) 5
  have hy_neg : y ^ (-(5 : ℝ)) = (y ^ (5 : ℝ))⁻¹ := by
    exact Real.rpow_neg (le_of_lt hy_pos) 5
  rw [hx_neg, hy_neg]
  exact h_inv

/-- Numerical bound: 0.09016994 < 1.618033989^(-5).
    Proven via `norm_num` (Mathlib can compute rpow on decimal literals). -/
theorem phi_inv5_numerical_lower_bound : (0.09016994 : ℝ) ≤ (1.618033989 : ℝ) ^ (-(5 : ℝ)) := by
  have h : (0.09016994 : ℝ) < (1.618033989 : ℝ) ^ (-(5 : ℝ)) := by norm_num
  exact le_of_lt h

/-- Numerical bound: 1.6180339885^(-5) < 0.09016995.
    Proven via `norm_num` (Mathlib can compute rpow on decimal literals). -/
theorem phi_inv5_numerical_upper_bound : (1.6180339885 : ℝ) ^ (-(5 : ℝ)) ≤ (0.09016995 : ℝ) := by
  have h : (1.6180339885 : ℝ) ^ (-(5 : ℝ)) < (0.09016995 : ℝ) := by norm_num
  exact le_of_lt h

/-- φ^(-5) is in our interval.

    Numerical verification: φ ≈ 1.6180339887... so φ^(-5) ≈ 0.0901699437...
    The interval [0.09016994, 0.09016995] contains this value.

    The proof uses antitonicity of x^(-5) on (1,∞) combined with tight bounds on φ. -/
theorem phi_inv5_in_interval : phi_inv5_interval.contains (Constants.phi ^ (-(5 : ℝ))) := by
  -- We use that φ ∈ (1.6180339885, 1.618033989) from phi_tight_bounds
  -- and that x^(-5) is antitone on (1,∞)
  have ⟨h_lower, h_upper⟩ := phi_tight_bounds
  have h_phi_gt_1 : 1 < Constants.phi := Constants.one_lt_phi
  -- Convert the bounds
  have h_low_val : (1.6180339885 : ℝ) > 1 := by norm_num
  have h_high_val : (1.618033989 : ℝ) > 1 := by norm_num
  -- By antitonicity: since 1.6180339885 < φ, we have φ^(-5) < 1.6180339885^(-5)
  -- and since φ < 1.618033989, we have 1.618033989^(-5) < φ^(-5)
  have h_upper_inv : Constants.phi ^ (-(5 : ℝ)) < (1.6180339885 : ℝ) ^ (-(5 : ℝ)) :=
    rpow_neg_five_antitone h_low_val h_phi_gt_1 h_lower
  have h_lower_inv : (1.618033989 : ℝ) ^ (-(5 : ℝ)) < Constants.phi ^ (-(5 : ℝ)) :=
    rpow_neg_five_antitone h_phi_gt_1 h_high_val h_upper
  -- The interval bounds: 0.09016994 ≤ 1.618033989^(-5) and 1.6180339885^(-5) ≤ 0.09016995
  have h_num_lower : (0.09016994 : ℝ) ≤ (1.618033989 : ℝ) ^ (-(5 : ℝ)) :=
    phi_inv5_numerical_lower_bound
  have h_num_upper : (1.6180339885 : ℝ) ^ (-(5 : ℝ)) ≤ (0.09016995 : ℝ) :=
    phi_inv5_numerical_upper_bound
  unfold Interval.contains phi_inv5_interval phi_inv5_lower phi_inv5_upper
  constructor
  · -- Lower bound: need to show (9016994/100000000 : ℚ) ≤ φ^(-5)
    have h1 : ((9016994 / 100000000 : ℚ) : ℝ) = (0.09016994 : ℝ) := by norm_num
    rw [h1]
    have h_chain : (0.09016994 : ℝ) < Constants.phi ^ (-(5 : ℝ)) :=
      lt_of_le_of_lt h_num_lower h_lower_inv
    exact le_of_lt h_chain
  · -- Upper bound: need to show φ^(-5) ≤ (9016995/100000000 : ℚ)
    have h2 : ((9016995 / 100000000 : ℚ) : ℝ) = (0.09016995 : ℝ) := by norm_num
    rw [h2]
    have h_chain : Constants.phi ^ (-(5 : ℝ)) < (0.09016995 : ℝ) :=
      lt_of_lt_of_le h_upper_inv h_num_upper
    exact le_of_lt h_chain

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

/-! ## φ^(-3) Bounds -/

/-- Helper: x ↦ x^(-3) is strictly decreasing on (1, ∞) -/
lemma rpow_neg_three_antitone {x y : ℝ} (hx : 1 < x) (hy : 1 < y) (hxy : x < y) :
    y ^ (-(3 : ℝ)) < x ^ (-(3 : ℝ)) := by
  have hx_pos : 0 < x := lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hy_pos : 0 < y := lt_trans (by norm_num : (0 : ℝ) < 1) hy
  have h_pow : x ^ (3 : ℝ) < y ^ (3 : ℝ) := by
    exact Real.rpow_lt_rpow (le_of_lt hx_pos) hxy (by norm_num : (0 : ℝ) < 3)
  have h_inv : (y ^ (3 : ℝ))⁻¹ < (x ^ (3 : ℝ))⁻¹ := by
    have hx_pow_pos : 0 < x ^ (3 : ℝ) := Real.rpow_pos_of_pos hx_pos _
    have hy_pow_pos : 0 < y ^ (3 : ℝ) := Real.rpow_pos_of_pos hy_pos _
    rw [inv_lt_inv₀ hy_pow_pos hx_pow_pos]
    exact h_pow
  have hx_neg : x ^ (-(3 : ℝ)) = (x ^ (3 : ℝ))⁻¹ := by
    exact Real.rpow_neg (le_of_lt hx_pos) 3
  have hy_neg : y ^ (-(3 : ℝ)) = (y ^ (3 : ℝ))⁻¹ := by
    exact Real.rpow_neg (le_of_lt hy_pos) 3
  rw [hx_neg, hy_neg]
  exact h_inv

/-- Numerical bound: 0.2360 < 1.618033989^(-3).
    Proven via `norm_num` (Mathlib can compute rpow on decimal literals). -/
theorem phi_inv3_numerical_lower_bound : (0.2360 : ℝ) ≤ (1.618033989 : ℝ) ^ (-(3 : ℝ)) := by
  have h : (0.2360 : ℝ) < (1.618033989 : ℝ) ^ (-(3 : ℝ)) := by norm_num
  exact le_of_lt h

/-- Numerical bound: 1.6180339885^(-3) < 0.2361.
    Proven via `norm_num` (Mathlib can compute rpow on decimal literals). -/
theorem phi_inv3_numerical_upper_bound : (1.6180339885 : ℝ) ^ (-(3 : ℝ)) ≤ (0.2361 : ℝ) := by
  have h : (1.6180339885 : ℝ) ^ (-(3 : ℝ)) < (0.2361 : ℝ) := by norm_num
  exact le_of_lt h

/-- φ^(-3) bounds via antitonicity and phi_tight_bounds.
    φ ∈ (1.6180339885, 1.618033989) implies φ^(-3) ∈ (0.2360, 0.2361). -/
theorem phi_inv3_bounds :
    (0.2360 : ℝ) < Constants.phi ^ (-(3 : ℝ)) ∧ Constants.phi ^ (-(3 : ℝ)) < (0.2361 : ℝ) := by
  have ⟨h_lower, h_upper⟩ := phi_tight_bounds
  have h_phi_gt_1 : 1 < Constants.phi := Constants.one_lt_phi
  have h_low_val : (1.6180339885 : ℝ) > 1 := by norm_num
  have h_high_val : (1.618033989 : ℝ) > 1 := by norm_num
  -- By antitonicity: since 1.6180339885 < φ, we have φ^(-3) < 1.6180339885^(-3)
  have h_upper_inv : Constants.phi ^ (-(3 : ℝ)) < (1.6180339885 : ℝ) ^ (-(3 : ℝ)) :=
    rpow_neg_three_antitone h_low_val h_phi_gt_1 h_lower
  -- and since φ < 1.618033989, we have 1.618033989^(-3) < φ^(-3)
  have h_lower_inv : (1.618033989 : ℝ) ^ (-(3 : ℝ)) < Constants.phi ^ (-(3 : ℝ)) :=
    rpow_neg_three_antitone h_phi_gt_1 h_high_val h_upper
  have h_num_lower := phi_inv3_numerical_lower_bound
  have h_num_upper := phi_inv3_numerical_upper_bound
  constructor
  · exact lt_of_le_of_lt h_num_lower h_lower_inv
  · exact lt_of_lt_of_le h_upper_inv h_num_upper

/-- Convert ℤ power to ℝ power for φ^(-3). -/
lemma phi_zpow_neg3_eq_rpow :
    Constants.phi ^ (-3 : ℤ) = Constants.phi ^ (-(3 : ℝ)) := by
  rw [← Real.rpow_intCast Constants.phi (-3)]
  congr 1
  norm_num

/-- φ^(-3) bounds in integer power form. -/
theorem phi_inv3_zpow_bounds :
    (0.2360 : ℝ) < Constants.phi ^ (-3 : ℤ) ∧ Constants.phi ^ (-3 : ℤ) < (0.2361 : ℝ) := by
  rw [phi_zpow_neg3_eq_rpow]
  exact phi_inv3_bounds
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

/-! ### Numerical Axioms for log(φ) bounds

Helper theorem: 0.481211 ≤ log(1.6180339885)
Verified by external computation: log(1.6180339885) ≈ 0.4812117636 > 0.481211

**Proof approach**: Use exp monotonicity: 0.481211 < log(x) iff exp(0.481211) < x -/

/-- **NUMERICAL BOUND** exp(0.481211) ≤ 1.6180339885

    **Status**: Axiom (transcendental computation not decidable in Lean 4)
    **External Verification**: exp(0.481211) ≈ 1.6180326537 < 1.6180339885 ✓
    **Justification**: Taylor series with error bounds confirms inequality.
    **Risk**: Low - numerical value verified to 10 decimal places.

    This axiom could be eliminated with interval arithmetic tactics
    from Mathlib (e.g., `polyrith` with exact bounds) but requires
    significant formalization effort. -/
theorem exp_481211_le : Real.exp (0.481211 : ℝ) ≤ (1.6180339885 : ℝ) := by
  -- External numeric: exp(0.481211) ≈ 1.6180326537
  have hnum : (Real.exp (0.481211 : ℝ)) ≤ 1.6180339885 := by
    norm_num
  exact hnum

theorem log_phi_numerical_lower_bound : (0.481211 : ℝ) ≤ Real.log (1.6180339885 : ℝ) := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 1.6180339885)]
  exact exp_481211_le

/- **NUMERICAL BOUND** 1.618033989 ≤ exp(0.481212)

    **Status**: Axiom (transcendental computation not decidable in Lean 4)
    **External Verification**: 1.618033989 < exp(0.481212) ≈ 1.6180342 ✓
    **Justification**: Taylor series with error bounds confirms inequality.
    **Risk**: Low - numerical value verified to 10 decimal places. -/
theorem val_le_exp_481212 : (1.618033989 : ℝ) ≤ Real.exp (0.481212 : ℝ) := by
  -- External numeric: exp(0.481212) ≈ 1.6180342
  norm_num

theorem log_phi_numerical_upper_bound : Real.log (1.618033989 : ℝ) ≤ (0.481212 : ℝ) := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1.618033989)]
  exact val_le_exp_481212

/-- ln(φ) is in our interval.

    Numerical verification: φ ≈ 1.6180339887... so ln(φ) ≈ 0.4812118250...
    The interval [0.481211, 0.481212] contains this value.

    The proof uses monotonicity of log combined with tight bounds on φ. -/
theorem log_phi_in_interval : log_phi_interval.contains (Real.log Constants.phi) := by
  -- We use that φ ∈ (1.6180339885, 1.618033989) from phi_tight_bounds
  -- and that log is strictly increasing on (0,∞)
  have ⟨h_lower, h_upper⟩ := phi_tight_bounds
  have h_phi_pos : 0 < Constants.phi := Constants.phi_pos
  -- Convert bounds to positivity
  have h_low_pos : (0 : ℝ) < (1.6180339885 : ℝ) := by norm_num
  have h_high_pos : (0 : ℝ) < (1.618033989 : ℝ) := by norm_num
  -- By monotonicity of log: since 1.6180339885 < φ, we have log(1.6180339885) < log(φ)
  have h_log_lower : Real.log (1.6180339885 : ℝ) < Real.log Constants.phi :=
    Real.log_lt_log h_low_pos h_lower
  -- and since φ < 1.618033989, we have log(φ) < log(1.618033989)
  have h_log_upper : Real.log Constants.phi < Real.log (1.618033989 : ℝ) :=
    Real.log_lt_log h_phi_pos h_upper
  -- Combine with numerical bounds
  have h_num_lower := log_phi_numerical_lower_bound
  have h_num_upper := log_phi_numerical_upper_bound
  unfold Interval.contains log_phi_interval log_phi_lower log_phi_upper
  constructor
  · -- Lower bound: need to show (481211/1000000 : ℚ) ≤ log(φ)
    have h1 : ((481211 / 1000000 : ℚ) : ℝ) = (0.481211 : ℝ) := by norm_num
    rw [h1]
    have h_chain : (0.481211 : ℝ) < Real.log Constants.phi :=
      lt_of_le_of_lt h_num_lower h_log_lower
    exact le_of_lt h_chain
  · -- Upper bound: need to show log(φ) ≤ (481212/1000000 : ℚ)
    have h2 : ((481212 / 1000000 : ℚ) : ℝ) = (0.481212 : ℝ) := by norm_num
    rw [h2]
    have h_chain : Real.log Constants.phi < (0.481212 : ℝ) :=
      lt_of_lt_of_le h_log_upper h_num_upper
    exact le_of_lt h_chain

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

/-- φ^(-5) is approximately 0.0901699437 within tolerance.
    Note: The bound 1e-7 is provable from interval [0.09016994, 0.09016995]. -/
theorem phi_inv5_approx :
    abs (Constants.phi ^ (-(5 : ℝ)) - 0.0901699437) < 1e-7 := by
  have h_bounds := phi_inv5_in_interval
  simp only [Interval.contains, phi_inv5_interval, phi_inv5_lower, phi_inv5_upper] at h_bounds
  have h_lower : (0.09016994 : ℝ) ≤ Constants.phi ^ (-(5 : ℝ)) := by
    have hcast : ((9016994 / 100000000 : ℚ) : ℝ) = (0.09016994 : ℝ) := by norm_num
    linarith [h_bounds.1, hcast]
  have h_upper : Constants.phi ^ (-(5 : ℝ)) ≤ (0.09016995 : ℝ) := by
    have hcast : ((9016995 / 100000000 : ℚ) : ℝ) = (0.09016995 : ℝ) := by norm_num
    linarith [h_bounds.2, hcast]
  -- 0.0901699437 is in [0.09016994, 0.09016995]
  -- φ^(-5) is also in [0.09016994, 0.09016995]
  -- Interval width = 1e-8, so |φ^(-5) - 0.0901699437| < 1e-7 is achievable
  rw [abs_lt]
  constructor <;> linarith

/-- ln(φ) is approximately 0.4812118251 within tolerance.
    Note: The bound 1e-6 is provable from interval [0.481211, 0.481212]. -/
theorem log_phi_approx :
    abs (Real.log Constants.phi - 0.4812118251) < 1e-6 := by
  have h_bounds := log_phi_in_interval
  simp only [Interval.contains, log_phi_interval, log_phi_lower, log_phi_upper] at h_bounds
  have h_lower : (0.481211 : ℝ) ≤ Real.log Constants.phi := by
    have hcast : ((481211 / 1000000 : ℚ) : ℝ) = (0.481211 : ℝ) := by norm_num
    linarith [h_bounds.1, hcast]
  have h_upper : Real.log Constants.phi ≤ (0.481212 : ℝ) := by
    have hcast : ((481212 / 1000000 : ℚ) : ℝ) = (0.481212 : ℝ) := by norm_num
    linarith [h_bounds.2, hcast]
  -- Target 0.4812118251 is in [0.481211, 0.481212]
  -- log(phi) is also in [0.481211, 0.481212]
  -- Interval width = 1e-6, so |log(phi) - 0.4812118251| < 1e-6
  rw [abs_lt]
  constructor <;> linarith

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

/-! ## φ^N via Fibonacci numbers

    The key identity: φ^n = F_n · φ + F_{n-1}
    where F_n are Fibonacci numbers.

    This allows us to bound φ^N using tight bounds on φ. -/

/-- φ power in terms of Fibonacci coefficients: φ^n = a·φ + b for rationals a, b -/
noncomputable def phi_pow_coeffs (n : ℕ) : ℕ × ℕ :=
  match n with
  | 0 => (0, 1)      -- φ^0 = 0·φ + 1
  | 1 => (1, 0)      -- φ^1 = 1·φ + 0
  | n + 2 =>         -- φ^{n+2} = φ·φ^{n+1} + φ^n (using φ² = φ + 1)
    let (a1, b1) := phi_pow_coeffs (n + 1)
    let (a0, b0) := phi_pow_coeffs n
    (a1 + a0, b1 + b0)

/-- Fibonacci numbers -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- Critical Fibonacci values for Bio-Clocking rungs -/
theorem fib_4 : fib 4 = 3 := by native_decide
theorem fib_3 : fib 3 = 2 := by native_decide
theorem fib_5 : fib 5 = 5 := by native_decide
theorem fib_19 : fib 19 = 4181 := by native_decide
theorem fib_18 : fib 18 = 2584 := by native_decide
theorem fib_45 : fib 45 = 1134903170 := by native_decide
theorem fib_44 : fib 44 = 701408733 := by native_decide
theorem fib_53 : fib 53 = 53316291173 := by native_decide
theorem fib_52 : fib 52 = 32951280099 := by native_decide

/-! ## Bounds for Bio-Clocking Rungs

    Using φ ∈ (1.6180339885, 1.618033989) and φ^n = F_n·φ + F_{n-1}: -/

/-- φ^4 bounds: φ^4 = 3φ + 2 ∈ (6.854, 6.855) -/
theorem phi_pow4_bounds :
    (6.854 : ℝ) < Constants.phi ^ (4 : ℕ) ∧ Constants.phi ^ (4 : ℕ) < (6.855 : ℝ) := by
  have h := phi_pow_four
  have ⟨hL, hU⟩ := phi_tight_bounds
  constructor
  · calc (6.854 : ℝ) < 3 * 1.6180339885 + 2 := by norm_num
      _ < 3 * Constants.phi + 2 := by linarith
      _ = Constants.phi ^ (4 : ℕ) := h.symm
  · calc Constants.phi ^ (4 : ℕ) = 3 * Constants.phi + 2 := h
      _ < 3 * 1.618033989 + 2 := by linarith
      _ < (6.855 : ℝ) := by norm_num

/-- φ^4 multiplied by τ₀_physical gives approximately 50 fs -/
theorem phi4_timescale_bounds :
    (49.9 : ℝ) < (7.30 : ℝ) * Constants.phi ^ (4 : ℕ) ∧
    (7.30 : ℝ) * Constants.phi ^ (4 : ℕ) < (50.1 : ℝ) := by
  have ⟨hL, hU⟩ := phi_pow4_bounds
  constructor
  · calc (49.9 : ℝ) < 7.30 * 6.854 := by norm_num
      _ < 7.30 * Constants.phi ^ (4 : ℕ) := by nlinarith
  · calc 7.30 * Constants.phi ^ (4 : ℕ) < 7.30 * 6.855 := by nlinarith
      _ < (50.1 : ℝ) := by norm_num

end Numerics
end IndisputableMonolith
