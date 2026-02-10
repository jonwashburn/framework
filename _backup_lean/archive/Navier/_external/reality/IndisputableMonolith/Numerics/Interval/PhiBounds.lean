import IndisputableMonolith.Numerics.Interval.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rigorous Bounds on the Golden Ratio

This module provides rigorous bounds on φ = (1 + √5)/2 using algebraic properties.

## Strategy

We use the fact that:
- 2.236² = 4.999696 < 5 < 5.001956 = 2.237²
- Therefore 2.236 < √5 < 2.237
- Therefore (1 + 2.236)/2 < φ < (1 + 2.237)/2
- i.e., 1.618 < φ < 1.6185

For tighter bounds, we use more decimal places.
-/

namespace IndisputableMonolith.Numerics

open Real

/-- 2.236² < 5 -/
theorem sq_2236_lt_5 : (2.236 : ℝ)^2 < 5 := by norm_num

/-- 5 < 2.237² -/
theorem five_lt_sq_2237 : (5 : ℝ) < (2.237 : ℝ)^2 := by norm_num

/-- 2.236 < √5 -/
theorem sqrt5_gt_2236 : (2.236 : ℝ) < sqrt 5 := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.236)]
  exact sqrt_lt_sqrt (by norm_num) sq_2236_lt_5

/-- √5 < 2.237 -/
theorem sqrt5_lt_2237 : sqrt 5 < (2.237 : ℝ) := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.237)]
  exact sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5) five_lt_sq_2237

/-- 1.618 < φ -/
theorem phi_gt_1618 : (1.618 : ℝ) < goldenRatio := by
  unfold goldenRatio
  have h : (2.236 : ℝ) < sqrt 5 := sqrt5_gt_2236
  linarith

/-- φ < 1.6185 -/
theorem phi_lt_16185 : goldenRatio < (1.6185 : ℝ) := by
  unfold goldenRatio
  have h : sqrt 5 < (2.237 : ℝ) := sqrt5_lt_2237
  linarith

-- For tighter bounds, we need more precision

/-- 2.2360679² < 5 -/
theorem sq_22360679_lt_5 : (2.2360679 : ℝ)^2 < 5 := by norm_num

/-- 5 < 2.2360680² -/
theorem five_lt_sq_22360680 : (5 : ℝ) < (2.2360680 : ℝ)^2 := by norm_num

/-- 2.2360679 < √5 -/
theorem sqrt5_gt_22360679 : (2.2360679 : ℝ) < sqrt 5 := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.2360679)]
  exact sqrt_lt_sqrt (by norm_num) sq_22360679_lt_5

/-- √5 < 2.2360680 -/
theorem sqrt5_lt_22360680 : sqrt 5 < (2.2360680 : ℝ) := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.2360680)]
  exact sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5) five_lt_sq_22360680

/-- 1.61803395 < φ -/
theorem phi_gt_161803395 : (1.61803395 : ℝ) < goldenRatio := by
  unfold goldenRatio
  have h : (2.2360679 : ℝ) < sqrt 5 := sqrt5_gt_22360679
  linarith

/-- φ < 1.6180340 -/
theorem phi_lt_16180340 : goldenRatio < (1.6180340 : ℝ) := by
  unfold goldenRatio
  have h : sqrt 5 < (2.2360680 : ℝ) := sqrt5_lt_22360680
  linarith

/-- Interval containing φ with tight bounds -/
def phiIntervalTight : Interval where
  lo := 161803395 / 100000000  -- 1.61803395
  hi := 16180340 / 10000000    -- 1.6180340
  valid := by norm_num

/-- φ is contained in phiIntervalTight - PROVEN -/
theorem phi_in_phiIntervalTight : phiIntervalTight.contains goldenRatio := by
  simp only [Interval.contains, phiIntervalTight]
  constructor
  · have h := phi_gt_161803395
    have h1 : ((161803395 / 100000000 : ℚ) : ℝ) < goldenRatio := by
      calc ((161803395 / 100000000 : ℚ) : ℝ) = (1.61803395 : ℝ) := by norm_num
        _ < goldenRatio := h
    exact le_of_lt h1
  · have h := phi_lt_16180340
    have h1 : goldenRatio < ((16180340 / 10000000 : ℚ) : ℝ) := by
      calc goldenRatio < (1.6180340 : ℝ) := h
        _ = ((16180340 / 10000000 : ℚ) : ℝ) := by norm_num
    exact le_of_lt h1

/-! ## Powers of φ using the recurrence φ² = φ + 1 -/

/-- φ² = φ + 1, so 2.618 < φ² < 2.619 -/
theorem phi_sq_gt : (2.618 : ℝ) < goldenRatio ^ 2 := by
  have h := phi_gt_1618
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  linarith

theorem phi_sq_lt : goldenRatio ^ 2 < (2.619 : ℝ) := by
  have h := phi_lt_16185
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  linarith

/-! ## φ^(-2) bounds (for quark masses) -/

/-- φ^(-2) > 0.3818 (using φ² < 2.619) -/
theorem phi_neg2_gt : (0.3818 : ℝ) < goldenRatio ^ (-2 : ℤ) := by
  have h := phi_sq_lt  -- φ² < 2.619
  have hpos : (0 : ℝ) < goldenRatio ^ 2 := by positivity
  have heq : goldenRatio ^ (-2 : ℤ) = (goldenRatio ^ 2)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 2)
  rw [heq]
  have h1 : (0.3818 : ℝ) < 1 / (2.619 : ℝ) := by norm_num
  have h2 : 1 / (2.619 : ℝ) < 1 / goldenRatio ^ 2 :=
    one_div_lt_one_div_of_lt hpos h
  have h3 : 1 / goldenRatio ^ 2 = (goldenRatio ^ 2)⁻¹ := one_div _
  linarith

/-- φ^(-2) < 0.382 (using φ² > 2.618) -/
theorem phi_neg2_lt : goldenRatio ^ (-2 : ℤ) < (0.382 : ℝ) := by
  have h := phi_sq_gt  -- 2.618 < φ²
  have hpos_bound : (0 : ℝ) < 2.618 := by norm_num
  have heq : goldenRatio ^ (-2 : ℤ) = (goldenRatio ^ 2)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 2)
  rw [heq]
  have h1 : (goldenRatio ^ 2)⁻¹ < (2.618 : ℝ)⁻¹ :=
    inv_strictAnti₀ hpos_bound h
  have h2 : (2.618 : ℝ)⁻¹ < (0.382 : ℝ) := by norm_num
  linarith

/-! ## Negative powers of φ (using φ⁻¹ = φ - 1) -/

/-- φ⁻¹ = φ - 1 ≈ 0.618 -/
theorem phi_inv_eq : goldenRatio⁻¹ = goldenRatio - 1 := by
  -- φ⁻¹ = -ψ = -(1 - √5)/2 = (√5 - 1)/2 = (1 + √5)/2 - 1 = φ - 1
  rw [inv_goldenRatio]
  unfold goldenRatio goldenConj
  ring

theorem phi_inv_gt : (0.618 : ℝ) < goldenRatio⁻¹ := by
  rw [phi_inv_eq]
  have h := phi_gt_1618
  linarith

theorem phi_inv_lt : goldenRatio⁻¹ < (0.6186 : ℝ) := by
  rw [phi_inv_eq]
  have h := phi_lt_16185
  linarith

/-- Interval containing φ⁻¹ - PROVEN -/
def phi_inv_interval_proven : Interval where
  lo := 618 / 1000
  hi := 6186 / 10000
  valid := by norm_num

theorem phi_inv_in_interval_proven : phi_inv_interval_proven.contains goldenRatio⁻¹ := by
  simp only [Interval.contains, phi_inv_interval_proven]
  constructor
  · have h := phi_inv_gt
    exact le_of_lt (by calc ((618 / 1000 : ℚ) : ℝ) = (0.618 : ℝ) := by norm_num
      _ < goldenRatio⁻¹ := h)
  · have h := phi_inv_lt
    exact le_of_lt (by calc goldenRatio⁻¹ < (0.6186 : ℝ) := h
      _ = ((6186 / 10000 : ℚ) : ℝ) := by norm_num)

/-! ## Higher powers using Fibonacci recurrence φ^(n+2) = φ^(n+1) + φ^n -/

/-- φ³ = φ² + φ = (φ + 1) + φ = 2φ + 1 -/
theorem phi_cubed_eq : goldenRatio ^ 3 = 2 * goldenRatio + 1 := by
  have h : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  calc goldenRatio ^ 3 = goldenRatio ^ 2 * goldenRatio := by ring
    _ = (goldenRatio + 1) * goldenRatio := by rw [h]
    _ = goldenRatio ^ 2 + goldenRatio := by ring
    _ = (goldenRatio + 1) + goldenRatio := by rw [h]
    _ = 2 * goldenRatio + 1 := by ring

theorem phi_cubed_gt : (4.236 : ℝ) < goldenRatio ^ 3 := by
  rw [phi_cubed_eq]
  have h := phi_gt_1618
  linarith

theorem phi_cubed_lt : goldenRatio ^ 3 < (4.237 : ℝ) := by
  rw [phi_cubed_eq]
  have h := phi_lt_16185
  linarith

/-- φ⁴ = φ³ + φ² = (2φ + 1) + (φ + 1) = 3φ + 2 -/
theorem phi_pow4_eq : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h3 : goldenRatio ^ 3 = 2 * goldenRatio + 1 := phi_cubed_eq
  calc goldenRatio ^ 4 = goldenRatio ^ 3 * goldenRatio := by ring
    _ = (2 * goldenRatio + 1) * goldenRatio := by rw [h3]
    _ = 2 * goldenRatio ^ 2 + goldenRatio := by ring
    _ = 2 * (goldenRatio + 1) + goldenRatio := by rw [h2]
    _ = 3 * goldenRatio + 2 := by ring

theorem phi_pow4_gt : (6.854 : ℝ) < goldenRatio ^ 4 := by
  rw [phi_pow4_eq]
  have h := phi_gt_1618
  linarith

theorem phi_pow4_lt : goldenRatio ^ 4 < (6.856 : ℝ) := by
  rw [phi_pow4_eq]
  have h := phi_lt_16185
  linarith

/-- φ⁵ = φ⁴ + φ³ = (3φ + 2) + (2φ + 1) = 5φ + 3 -/
theorem phi_pow5_eq : goldenRatio ^ 5 = 5 * goldenRatio + 3 := by
  have h3 : goldenRatio ^ 3 = 2 * goldenRatio + 1 := phi_cubed_eq
  have h4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := phi_pow4_eq
  calc goldenRatio ^ 5 = goldenRatio ^ 4 * goldenRatio := by ring
    _ = (3 * goldenRatio + 2) * goldenRatio := by rw [h4]
    _ = 3 * goldenRatio ^ 2 + 2 * goldenRatio := by ring
    _ = 3 * (goldenRatio + 1) + 2 * goldenRatio := by rw [goldenRatio_sq]
    _ = 5 * goldenRatio + 3 := by ring

theorem phi_pow5_gt : (11.09 : ℝ) < goldenRatio ^ 5 := by
  rw [phi_pow5_eq]
  have h := phi_gt_1618
  linarith

theorem phi_pow5_lt : goldenRatio ^ 5 < (11.1 : ℝ) := by
  rw [phi_pow5_eq]
  have h := phi_lt_16185
  linarith

/-- φ⁸ = F₈·φ + F₇ = 21φ + 13 (where F_n is Fibonacci) -/
theorem phi_pow8_eq : goldenRatio ^ 8 = 21 * goldenRatio + 13 := by
  -- φ⁶ = 8φ + 5, φ⁷ = 13φ + 8, φ⁸ = 21φ + 13
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := phi_pow4_eq
  calc goldenRatio ^ 8 = goldenRatio ^ 4 * goldenRatio ^ 4 := by ring
    _ = (3 * goldenRatio + 2) * (3 * goldenRatio + 2) := by rw [h4]
    _ = 9 * goldenRatio ^ 2 + 12 * goldenRatio + 4 := by ring
    _ = 9 * (goldenRatio + 1) + 12 * goldenRatio + 4 := by rw [h2]
    _ = 21 * goldenRatio + 13 := by ring

theorem phi_pow8_gt : (46.97 : ℝ) < goldenRatio ^ 8 := by
  rw [phi_pow8_eq]
  have h := phi_gt_1618
  linarith

theorem phi_pow8_lt : goldenRatio ^ 8 < (46.99 : ℝ) := by
  rw [phi_pow8_eq]
  have h := phi_lt_16185
  linarith

/-- Interval containing φ⁸ - PROVEN -/
def phi_pow8_interval_proven : Interval where
  lo := 4697 / 100
  hi := 4699 / 100
  valid := by norm_num

theorem phi_pow8_in_interval_proven : phi_pow8_interval_proven.contains (goldenRatio ^ 8) := by
  simp only [Interval.contains, phi_pow8_interval_proven]
  constructor
  · have h := phi_pow8_gt
    exact le_of_lt (by calc ((4697 / 100 : ℚ) : ℝ) = (46.97 : ℝ) := by norm_num
      _ < goldenRatio ^ 8 := h)
  · have h := phi_pow8_lt
    exact le_of_lt (by calc goldenRatio ^ 8 < (46.99 : ℝ) := h
      _ = ((4699 / 100 : ℚ) : ℝ) := by norm_num)

/-! ## Negative powers using (φ⁻¹)^n -/

/-- (φ⁻¹)² bounds -/
theorem phi_inv2_gt : (0.381 : ℝ) < goldenRatio⁻¹ ^ 2 := by
  have h := phi_inv_gt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  nlinarith [sq_nonneg goldenRatio⁻¹]

theorem phi_inv2_lt : goldenRatio⁻¹ ^ 2 < (0.383 : ℝ) := by
  have h := phi_inv_lt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  nlinarith [sq_nonneg goldenRatio⁻¹]

/-- (φ⁻¹)³ bounds -/
theorem phi_inv3_gt : (0.2359 : ℝ) < goldenRatio⁻¹ ^ 3 := by
  have h1 := phi_inv_gt
  have h2 := phi_inv2_gt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  have hpos2 : 0 < goldenRatio⁻¹ ^ 2 := sq_pos_of_pos hpos
  nlinarith [sq_nonneg goldenRatio⁻¹]

theorem phi_inv3_lt : goldenRatio⁻¹ ^ 3 < (0.237 : ℝ) := by
  have h1 := phi_inv_lt
  have h2 := phi_inv2_lt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  nlinarith [sq_nonneg goldenRatio⁻¹]

/-- Interval containing (φ⁻¹)³ - PROVEN -/
def phi_inv3_interval_proven : Interval where
  lo := 2359 / 10000
  hi := 237 / 1000
  valid := by norm_num

theorem phi_inv3_in_interval_proven : phi_inv3_interval_proven.contains (goldenRatio⁻¹ ^ 3) := by
  simp only [Interval.contains, phi_inv3_interval_proven]
  constructor
  · have h := phi_inv3_gt
    exact le_of_lt (by calc ((2359 / 10000 : ℚ) : ℝ) = (0.2359 : ℝ) := by norm_num
      _ < goldenRatio⁻¹ ^ 3 := h)
  · have h := phi_inv3_lt
    exact le_of_lt (by calc goldenRatio⁻¹ ^ 3 < (0.237 : ℝ) := h
      _ = ((237 / 1000 : ℚ) : ℝ) := by norm_num)

/-- (φ⁻¹)⁵ bounds - using 0.381 * 0.2359 ≈ 0.0899 -/
theorem phi_inv5_gt : (0.089 : ℝ) < goldenRatio⁻¹ ^ 5 := by
  have h2 := phi_inv2_gt
  have h3 := phi_inv3_gt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  have hpos2 : 0 < goldenRatio⁻¹ ^ 2 := sq_pos_of_pos hpos
  have hpos3 : 0 < goldenRatio⁻¹ ^ 3 := pow_pos hpos 3
  have h : goldenRatio⁻¹ ^ 5 = goldenRatio⁻¹ ^ 2 * goldenRatio⁻¹ ^ 3 := by ring
  nlinarith

theorem phi_inv5_lt : goldenRatio⁻¹ ^ 5 < (0.091 : ℝ) := by
  have h2 := phi_inv2_lt
  have h3 := phi_inv3_lt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  have hpos2 : 0 < goldenRatio⁻¹ ^ 2 := sq_pos_of_pos hpos
  have hpos3 : 0 < goldenRatio⁻¹ ^ 3 := pow_pos hpos 3
  have h : goldenRatio⁻¹ ^ 5 = goldenRatio⁻¹ ^ 2 * goldenRatio⁻¹ ^ 3 := by ring
  nlinarith

/-- Interval containing (φ⁻¹)⁵ - PROVEN -/
def phi_inv5_interval_proven : Interval where
  lo := 89 / 1000
  hi := 91 / 1000
  valid := by norm_num

theorem phi_inv5_in_interval_proven : phi_inv5_interval_proven.contains (goldenRatio⁻¹ ^ 5) := by
  simp only [Interval.contains, phi_inv5_interval_proven]
  constructor
  · have h := phi_inv5_gt
    exact le_of_lt (by calc ((89 / 1000 : ℚ) : ℝ) = (0.089 : ℝ) := by norm_num
      _ < goldenRatio⁻¹ ^ 5 := h)
  · have h := phi_inv5_lt
    exact le_of_lt (by calc goldenRatio⁻¹ ^ 5 < (0.091 : ℝ) := h
      _ = ((91 / 1000 : ℚ) : ℝ) := by norm_num)

/-! ## Higher powers for φ^16 -/

/-- φ^16 = F₁₆·φ + F₁₅ = 987φ + 610 -/
theorem phi_pow16_eq : goldenRatio ^ 16 = 987 * goldenRatio + 610 := by
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h8 : goldenRatio ^ 8 = 21 * goldenRatio + 13 := phi_pow8_eq
  calc goldenRatio ^ 16 = goldenRatio ^ 8 * goldenRatio ^ 8 := by ring
    _ = (21 * goldenRatio + 13) * (21 * goldenRatio + 13) := by rw [h8]
    _ = 441 * goldenRatio ^ 2 + 546 * goldenRatio + 169 := by ring
    _ = 441 * (goldenRatio + 1) + 546 * goldenRatio + 169 := by rw [h2]
    _ = 987 * goldenRatio + 610 := by ring

theorem phi_pow16_gt : (1596.9 : ℝ) < goldenRatio ^ 16 := by
  rw [phi_pow16_eq]
  have h := phi_gt_1618
  -- 987 * 1.618 + 610 = 1596.166 + 610 = 2206.166
  -- Wait that's > 1596.9
  linarith

theorem phi_pow16_lt : goldenRatio ^ 16 < (2208 : ℝ) := by
  rw [phi_pow16_eq]
  have h := phi_lt_16185
  -- 987 * 1.6185 + 610 = 1597.0595 + 610 = 2207.0595 < 2208
  linarith

/-- φ^51 = F₅₁·φ + F₅₀ = 20365011074·φ + 12586269025 -/
theorem phi_pow51_eq : goldenRatio ^ 51 = 20365011074 * goldenRatio + 12586269025 := by
  have h :=
    (Real.goldenRatio_mul_fib_succ_add_fib 50 :
        goldenRatio * (Nat.fib 51 : ℝ) + Nat.fib 50 = goldenRatio ^ 51)
  have fib51 : (Nat.fib 51 : ℝ) = 20365011074 := by norm_num
  have fib50 : (Nat.fib 50 : ℝ) = 12586269025 := by norm_num
  simpa [fib51, fib50, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc] using h.symm

theorem phi_pow51_gt : (45537548334 : ℝ) < goldenRatio ^ 51 := by
  rw [phi_pow51_eq]
  -- We need: 45537548334 < 20365011074 * φ + 12586269025
  -- i.e., 32951279309 < 20365011074 * φ
  -- Our bound: φ > 1.61803395
  -- 20365011074 * 1.61803395 = 32951279309.857... > 32951279309 ✓
  have hphi := phi_gt_161803395
  have h1 : (32951279309 : ℝ) < (20365011074 : ℝ) * (161803395 / 100000000 : ℝ) := by norm_num
  have h2 : (161803395 / 100000000 : ℝ) < goldenRatio := by
    have heq : (161803395 / 100000000 : ℝ) = (1.61803395 : ℝ) := by norm_num
    rw [heq]
    exact hphi
  have h3 : (20365011074 : ℝ) * (161803395 / 100000000 : ℝ) < (20365011074 : ℝ) * goldenRatio :=
    mul_lt_mul_of_pos_left h2 (by norm_num : (0 : ℝ) < 20365011074)
  -- 45537548334 - 12586269025 = 32951279309
  linarith

theorem phi_pow51_lt : goldenRatio ^ 51 < (45537549354 : ℝ) := by
  rw [phi_pow51_eq]
  -- We need: 20365011074 * φ + 12586269025 < 45537549354
  -- i.e., 20365011074 * φ < 32951280329
  -- Our bound: φ < 1.6180340
  -- 20365011074 * 1.6180340 = 32951280328.108... < 32951280329 ✓
  have hphi := phi_lt_16180340
  have h1 : goldenRatio < (16180340 / 10000000 : ℝ) := by
    have heq : (16180340 / 10000000 : ℝ) = (1.6180340 : ℝ) := by norm_num
    rw [heq]
    exact hphi
  have h2 : (20365011074 : ℝ) * goldenRatio < (20365011074 : ℝ) * (16180340 / 10000000 : ℝ) :=
    mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 20365011074)
  have h3 : (20365011074 : ℝ) * (16180340 / 10000000 : ℝ) < (32951280329 : ℝ) := by norm_num
  -- 32951280329 + 12586269025 = 45537549354
  linarith

def phi_pow51_interval_proven : Interval where
  lo := 45537548334
  hi := 45537549354
  valid := by norm_num

theorem phi_pow51_in_interval_proven :
    phi_pow51_interval_proven.contains (goldenRatio ^ 51) := by
  simp [Interval.contains, phi_pow51_interval_proven, phi_pow51_gt, phi_pow51_lt, le_of_lt]

/-! ## φ^54 bounds (for neutrino mass predictions) -/

/-- φ^54 = φ^51 × φ^3 -/
theorem phi_pow54_eq : goldenRatio ^ 54 = goldenRatio ^ 51 * goldenRatio ^ 3 := by
  ring_nf

/-- φ^54 > 192897054742 (using φ^51 > 45537548334 and φ^3 > 4.236) -/
theorem phi_pow54_gt : (192897054742 : ℝ) < goldenRatio ^ 54 := by
  rw [phi_pow54_eq]
  have h51 := phi_pow51_gt  -- 45537548334 < φ^51
  have h3 := phi_cubed_gt   -- 4.236 < φ^3
  have hpos51 : (0 : ℝ) < goldenRatio ^ 51 := by positivity
  have hpos3 : (0 : ℝ) < goldenRatio ^ 3 := by positivity
  -- 45537548334 * 4.236 = 192897054743.224 > 192897054742
  calc (192897054742 : ℝ) < (45537548334 : ℝ) * (4.236 : ℝ) := by norm_num
    _ < goldenRatio ^ 51 * (4.236 : ℝ) := by nlinarith
    _ < goldenRatio ^ 51 * goldenRatio ^ 3 := by nlinarith

/-- φ^54 < 192942596613 (using φ^51 < 45537549354 and φ^3 < 4.237) -/
theorem phi_pow54_lt : goldenRatio ^ 54 < (192942596613 : ℝ) := by
  rw [phi_pow54_eq]
  have h51 := phi_pow51_lt  -- φ^51 < 45537549354
  have h3 := phi_cubed_lt   -- φ^3 < 4.237
  have hpos51 : (0 : ℝ) < goldenRatio ^ 51 := by positivity
  have hpos3 : (0 : ℝ) < goldenRatio ^ 3 := by positivity
  -- 45537549354 * 4.237 = 192942596612.898 < 192942596613
  calc goldenRatio ^ 51 * goldenRatio ^ 3 < (45537549354 : ℝ) * goldenRatio ^ 3 := by nlinarith
    _ < (45537549354 : ℝ) * (4.237 : ℝ) := by nlinarith
    _ < (192942596613 : ℝ) := by norm_num

/-! ## φ^(-54) bounds (for neutrino mass predictions) -/

/-- φ^(-54) > 5.182e-12 (using φ^54 < 192942596613) -/
theorem phi_neg54_gt : (5.182e-12 : ℝ) < goldenRatio ^ (-54 : ℤ) := by
  have h := phi_pow54_lt  -- φ^54 < 192942596613
  have hpos : (0 : ℝ) < goldenRatio ^ 54 := by positivity
  have heq : goldenRatio ^ (-54 : ℤ) = (goldenRatio ^ 54)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 54)
  rw [heq]
  -- 1/192942596613 > 5.182e-12
  have h1 : (5.182e-12 : ℝ) < 1 / (192942596613 : ℝ) := by norm_num
  have h2 : 1 / (192942596613 : ℝ) < 1 / goldenRatio ^ 54 :=
    one_div_lt_one_div_of_lt hpos h
  have h3 : 1 / goldenRatio ^ 54 = (goldenRatio ^ 54)⁻¹ := one_div _
  linarith

/-- φ^(-54) < 5.185e-12 (using φ^54 > 192897054742) -/
theorem phi_neg54_lt : goldenRatio ^ (-54 : ℤ) < (5.185e-12 : ℝ) := by
  have h := phi_pow54_gt  -- 192897054742 < φ^54
  have hpos_bound : (0 : ℝ) < 192897054742 := by norm_num
  have heq : goldenRatio ^ (-54 : ℤ) = (goldenRatio ^ 54)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 54)
  rw [heq]
  -- 1/192897054742 < 5.185e-12
  have h1 : (goldenRatio ^ 54)⁻¹ < (192897054742 : ℝ)⁻¹ :=
    inv_strictAnti₀ hpos_bound h
  have h2 : (192897054742 : ℝ)⁻¹ < (5.185e-12 : ℝ) := by norm_num
  linarith

/-! ## φ^58 bounds (for neutrino mass predictions) -/

/-- φ^58 = φ^54 × φ^4 -/
theorem phi_pow58_eq : goldenRatio ^ 58 = goldenRatio ^ 54 * goldenRatio ^ 4 := by
  ring_nf

/-- φ^58 > 1.322e12 (using φ^54 > 192897054742 and φ^4 > 6.854) -/
theorem phi_pow58_gt : (1.322e12 : ℝ) < goldenRatio ^ 58 := by
  rw [phi_pow58_eq]
  have h54 := phi_pow54_gt  -- 192897054742 < φ^54
  have h4 := phi_pow4_gt    -- 6.854 < φ^4
  have hpos54 : (0 : ℝ) < goldenRatio ^ 54 := by positivity
  have hpos4 : (0 : ℝ) < goldenRatio ^ 4 := by positivity
  -- 192897054742 * 6.854 = 1.322e12
  calc (1.322e12 : ℝ) < (192897054742 : ℝ) * (6.854 : ℝ) := by norm_num
    _ < goldenRatio ^ 54 * (6.854 : ℝ) := by nlinarith
    _ < goldenRatio ^ 54 * goldenRatio ^ 4 := by nlinarith

/-- φ^58 < 1.324e12 (using φ^54 < 192942596613 and φ^4 < 6.86) -/
theorem phi_pow58_lt : goldenRatio ^ 58 < (1.324e12 : ℝ) := by
  rw [phi_pow58_eq]
  have h54 := phi_pow54_lt  -- φ^54 < 192942596613
  have h4 := phi_pow4_lt    -- φ^4 < 6.86
  have hpos54 : (0 : ℝ) < goldenRatio ^ 54 := by positivity
  have hpos4 : (0 : ℝ) < goldenRatio ^ 4 := by positivity
  calc goldenRatio ^ 54 * goldenRatio ^ 4 < (192942596613 : ℝ) * goldenRatio ^ 4 := by nlinarith
    _ < (192942596613 : ℝ) * (6.86 : ℝ) := by nlinarith
    _ < (1.324e12 : ℝ) := by norm_num

/-! ## φ^(-58) bounds (for neutrino mass predictions) -/

/-- φ^(-58) > 7.55e-13 (using φ^58 < 1.324e12) -/
theorem phi_neg58_gt : (7.55e-13 : ℝ) < goldenRatio ^ (-58 : ℤ) := by
  have h := phi_pow58_lt  -- φ^58 < 1.324e12
  have hpos : (0 : ℝ) < goldenRatio ^ 58 := by positivity
  have heq : goldenRatio ^ (-58 : ℤ) = (goldenRatio ^ 58)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 58)
  rw [heq]
  have h1 : (7.55e-13 : ℝ) < 1 / (1.324e12 : ℝ) := by norm_num
  have h2 : 1 / (1.324e12 : ℝ) < 1 / goldenRatio ^ 58 :=
    one_div_lt_one_div_of_lt hpos h
  have h3 : 1 / goldenRatio ^ 58 = (goldenRatio ^ 58)⁻¹ := one_div _
  linarith

/-- φ^(-58) < 7.57e-13 (using φ^58 > 1.322e12) -/
theorem phi_neg58_lt : goldenRatio ^ (-58 : ℤ) < (7.57e-13 : ℝ) := by
  have h := phi_pow58_gt  -- 1.322e12 < φ^58
  have hpos_bound : (0 : ℝ) < 1.322e12 := by norm_num
  have heq : goldenRatio ^ (-58 : ℤ) = (goldenRatio ^ 58)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 58)
  rw [heq]
  have h1 : (goldenRatio ^ 58)⁻¹ < (1.322e12 : ℝ)⁻¹ :=
    inv_strictAnti₀ hpos_bound h
  have h2 : (1.322e12 : ℝ)⁻¹ < (7.57e-13 : ℝ) := by norm_num
  linarith

/-! ## φ − 1 bounds (preparation for log φ analysis) -/

lemma phi_sub_one_pos : 0 < goldenRatio - 1 := by
  have h := phi_gt_1618
  linarith

lemma phi_sub_one_lt_one : goldenRatio - 1 < 1 := by
  have h := Real.goldenRatio_lt_two
  linarith

lemma phi_sub_one_mem_Icc : goldenRatio - 1 ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_of_lt phi_sub_one_pos, le_of_lt phi_sub_one_lt_one⟩

end IndisputableMonolith.Numerics
