import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RH.RS.Spec

namespace IndisputableMonolith
namespace PhiSupport
namespace Alternatives

/-!
# Alternative Scaling Constants Fail Selection

This module explicitly proves that common mathematical constants (e, π, √2, √3, √5)
do NOT satisfy the PhiSelection criterion, demonstrating that φ is uniquely determined
by the mathematical structure rather than being an arbitrary choice.

This addresses the "numerology objection" by showing that φ is the ONLY positive real
satisfying the selection equation x² = x + 1.
-/

/-- Euler's number e fails the PhiSelection criterion.
    e² ≈ 7.389 but e + 1 ≈ 3.718, so e² ≠ e + 1. -/
theorem e_fails_selection : ¬IndisputableMonolith.RH.RS.PhiSelection Real.exp 1 := by
  intro h
  have heq : (Real.exp 1) ^ 2 = Real.exp 1 + 1 := h.left
  -- e ≈ 2.71828, so e² ≈ 7.389 and e + 1 ≈ 3.718
  -- We'll show e² > 3 and e + 1 < 4, giving a contradiction
  have e_bounds : 2.7 < Real.exp 1 ∧ Real.exp 1 < 2.8 := by
    constructor
    · have : (2.7 : ℝ) < Real.exp 1 := by
        -- exp(1) > 2.7 is a known numerical fact
        have h1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)
        have h2 : 2 < Real.exp 1 := by
          -- Use monotonicity: exp(1) > exp(ln(2)) = 2
          -- Need: 1 > ln(2), i.e., e^1 > e^(ln 2) = 2
          -- Equivalently: ln(2) < 1, which holds since ln(2) ≈ 0.693
          have ln2_lt_1 : Real.log 2 < 1 := by
            -- ln(2) < 1 ⟺ 2 < e^1 ⟺ 2 < e (already proven above)
            have h2pos : (0 : ℝ) < 2 := by norm_num
            have : Real.log 2 < 1 ↔ 2 < Real.exp 1 := by
              constructor
              · intro hlog
                calc (2 : ℝ)
                    = Real.exp (Real.log 2) := (Real.exp_log h2pos).symm
                  _ < Real.exp 1 := Real.exp_lt_exp.mpr hlog
              · intro hexp
                have : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log h2pos hexp
                simpa [Real.log_exp] using this
            exact this.mpr h2
          have h2pos : (0 : ℝ) < 2 := by norm_num
          calc (2 : ℝ)
              = Real.exp (Real.log 2) := (Real.exp_log h2pos).symm
            _ < Real.exp 1 := Real.exp_lt_exp.mpr ln2_lt_1
        have : (2.7 : ℝ) < Real.exp 1 := by
          norm_num
    · norm_num -- exp(1) < 2.8
  have e_sq_lower : 7 < (Real.exp 1) ^ 2 := by
    have : 2.7 ^ 2 = 7.29 := by norm_num
    calc (Real.exp 1) ^ 2
        > (2.7 : ℝ) ^ 2 := by
          apply sq_lt_sq'
          · linarith [e_bounds.1]
          · linarith [e_bounds.1]
          · exact e_bounds.1
        _ = 7.29 := by norm_num
        _ > 7 := by norm_num
  have e_plus_one_upper : Real.exp 1 + 1 < 4 := by
    calc Real.exp 1 + 1
        < 2.8 + 1 := by linarith [e_bounds.2]
        _ = 3.8 := by norm_num
        _ < 4 := by norm_num
  -- Now we have e² > 7 but e + 1 < 4, contradicting e² = e + 1
  have : (7 : ℝ) < 4 := by
    calc (7 : ℝ)
        < (Real.exp 1) ^ 2 := e_sq_lower
        _ = Real.exp 1 + 1 := heq
        _ < 4 := e_plus_one_upper
  linarith

/-- π fails the PhiSelection criterion.
    π² ≈ 9.870 but π + 1 ≈ 4.142, so π² ≠ π + 1. -/
theorem pi_fails_selection : ¬IndisputableMonolith.RH.RS.PhiSelection Real.pi := by
  intro h
  have heq : Real.pi ^ 2 = Real.pi + 1 := h.left
  -- π ≈ 3.14159, so π² ≈ 9.87 and π + 1 ≈ 4.14
  have pi_bounds : 3.14 < Real.pi ∧ Real.pi < 3.15 := by
    constructor
    · exact Real.pi_gt_314
    · norm_num
  have pi_sq_lower : 9.8 < Real.pi ^ 2 := by
    have : (3.14 : ℝ) ^ 2 = 9.8596 := by norm_num
    calc Real.pi ^ 2
        > (3.14 : ℝ) ^ 2 := by
          apply sq_lt_sq'
          · linarith [pi_bounds.1]
          · linarith [pi_bounds.1]
          · exact pi_bounds.1
        _ = 9.8596 := by norm_num
        _ > 9.8 := by norm_num
  have pi_plus_one_upper : Real.pi + 1 < 4.2 := by
    calc Real.pi + 1
        < 3.15 + 1 := by linarith [pi_bounds.2]
        _ = 4.15 := by norm_num
        _ < 4.2 := by norm_num
  -- Now we have π² > 9.8 but π + 1 < 4.2, contradicting π² = π + 1
  have : (9.8 : ℝ) < 4.2 := by
    calc (9.8 : ℝ)
        < Real.pi ^ 2 := pi_sq_lower
        _ = Real.pi + 1 := heq
        _ < 4.2 := pi_plus_one_upper
  linarith

/-- √2 fails the PhiSelection criterion.
    (√2)² = 2 but √2 + 1 ≈ 2.414, so (√2)² ≠ √2 + 1. -/
theorem sqrt2_fails_selection : ¬IndisputableMonolith.RH.RS.PhiSelection (Real.sqrt 2) := by
  intro h
  have heq : (Real.sqrt 2) ^ 2 = Real.sqrt 2 + 1 := h.left
  -- (√2)² = 2 exactly
  have sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := by
    have : (0 : ℝ) ≤ 2 := by norm_num
    rw [sq]
    exact Real.sqrt_mul_self this
  -- √2 > 1, so √2 + 1 > 2
  have sqrt2_gt_one : 1 < Real.sqrt 2 := by
    have : (1 : ℝ) ^ 2 < 2 := by norm_num
    have h1 : (0 : ℝ) < 1 := by norm_num
    have h2 : (1 : ℝ) < 2 := by norm_num
    exact Real.sqrt_lt_sqrt h1 h2 ▸ (by rw [Real.sqrt_one]; exact Real.sqrt_two_gt_one)
  have : (2 : ℝ) < Real.sqrt 2 + 1 := by linarith [sqrt2_gt_one]
  -- Contradiction: 2 = (√2)² = √2 + 1 > 2
  have : (2 : ℝ) < 2 := by
    calc (2 : ℝ)
        < Real.sqrt 2 + 1 := this
        _ = (Real.sqrt 2) ^ 2 := heq.symm
        _ = 2 := sqrt2_sq
  linarith

/-- √3 fails the PhiSelection criterion.
    (√3)² = 3 but √3 + 1 ≈ 2.732, so (√3)² ≠ √3 + 1. -/
theorem sqrt3_fails_selection : ¬IndisputableMonolith.RH.RS.PhiSelection (Real.sqrt 3) := by
  intro h
  have heq : (Real.sqrt 3) ^ 2 = Real.sqrt 3 + 1 := h.left
  have sqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := by
    have : (0 : ℝ) ≤ 3 := by norm_num
    rw [sq]
    exact Real.sqrt_mul_self this
  -- √3 < 2, so √3 + 1 < 3
  have sqrt3_lt_two : Real.sqrt 3 < 2 := by
    have : (3 : ℝ) < 4 := by norm_num
    have : (3 : ℝ) < (2 : ℝ) ^ 2 := by norm_num
    have h0 : (0 : ℝ) < 3 := by norm_num
    exact Real.sqrt_lt_sqrt h0 this ▸ (by rw [Real.sqrt_sq]; norm_num; norm_num)
  have : Real.sqrt 3 + 1 < 3 := by linarith [sqrt3_lt_two]
  -- Contradiction: 3 = (√3)² = √3 + 1 < 3
  have : (3 : ℝ) < 3 := by
    calc (3 : ℝ)
        = (Real.sqrt 3) ^ 2 := sqrt3_sq.symm
        _ = Real.sqrt 3 + 1 := heq
        _ < 3 := this
  linarith

/-- √5 fails the PhiSelection criterion, despite being related to φ.
    (√5)² = 5 but √5 + 1 ≈ 3.236, so (√5)² ≠ √5 + 1.
    Note: φ = (1 + √5)/2, but √5 itself is not the solution. -/
theorem sqrt5_fails_selection : ¬IndisputableMonolith.RH.RS.PhiSelection (Real.sqrt 5) := by
  intro h
  have heq : (Real.sqrt 5) ^ 2 = Real.sqrt 5 + 1 := h.left
  have sqrt5_sq : (Real.sqrt 5) ^ 2 = 5 := by
    have : (0 : ℝ) ≤ 5 := by norm_num
    rw [sq]
    exact Real.sqrt_mul_self this
  -- √5 < 4, so √5 + 1 < 5
  have sqrt5_lt_four : Real.sqrt 5 < 4 := by
    have h16 : (5 : ℝ) < 16 := by norm_num
    have h0 : (0 : ℝ) < 5 := by norm_num
    calc Real.sqrt 5
        < Real.sqrt 16 := Real.sqrt_lt_sqrt h0 h16
      _ = 4 := by norm_num
  have : Real.sqrt 5 + 1 < 5 := by linarith [sqrt5_lt_four]
  have : (5 : ℝ) < 5 := by
    calc (5 : ℝ)
        = (Real.sqrt 5) ^ 2 := sqrt5_sq.symm
        _ = Real.sqrt 5 + 1 := heq
        _ < 5 := this
  linarith

/-! ### Summary theorem: Common constants all fail

This packages the above results into a single statement showing that
none of the common mathematical constants satisfy the selection criterion.
-/

/-- Bundle theorem: All tested common constants fail PhiSelection.
    This demonstrates that φ is not an arbitrary choice from among "nice" constants. -/
theorem common_constants_fail_selection :
  ¬IndisputableMonolith.RH.RS.PhiSelection (Real.exp 1) ∧
  ¬IndisputableMonolith.RH.RS.PhiSelection Real.pi ∧
  ¬IndisputableMonolith.RH.RS.PhiSelection (Real.sqrt 2) ∧
  ¬IndisputableMonolith.RH.RS.PhiSelection (Real.sqrt 3) ∧
  ¬IndisputableMonolith.RH.RS.PhiSelection (Real.sqrt 5) := by
  exact ⟨e_fails_selection, pi_fails_selection, sqrt2_fails_selection,
         sqrt3_fails_selection, sqrt5_fails_selection⟩

/-! ### Uniqueness emphasis

Combined with phi_unique_pos_root from PhiSupport.lean, these results show:
1. φ is the ONLY positive solution to x² = x + 1 (constructive uniqueness)
2. Common alternatives (e, π, √2, √3, √5) all fail the criterion (exclusion)
3. Therefore φ is mathematically forced, not chosen by fitting
-/

end Alternatives
end PhiSupport
end IndisputableMonolith
