/-!
Compatibility shims and common mathlib imports.

This module collects small alias lemmas and helpers to stabilize names
across mathlib versions and reduce duplication across the codebase.
-/

import Mathlib/Analysis/SpecialFunctions/Pow/Real
import Mathlib/Analysis/SpecialFunctions/Log
import Mathlib/Analysis/NormedSpace/Matrix
import Mathlib/Data/Complex/Basic
import Mathlib/Data/Complex/Exponential
import Mathlib/LinearAlgebra/Matrix/ToLinearEquiv
import Mathlib/Tactic

open scoped BigOperators Matrix
open Real Complex

-- Aliases and small helpers

@[simp] theorem inv_eq_one_div (x : ℝ) : x⁻¹ = 1 / x := by
  simp [one_div]

theorem one_div_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < 1 / x := by
  simpa [one_div] using inv_pos.mpr hx

theorem one_div_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 / x := by
  simpa [one_div] using inv_nonneg.mpr hx

theorem Real.rpow_nonneg_of_nonneg {x a : ℝ} (hx : 0 ≤ x) : 0 ≤ x ^ a := by
  simpa using Real.rpow_nonneg hx a

theorem Real.rpow_lt_one_of_pos_of_lt_one {x y : ℝ}
    (hx_pos : 0 < x) (hx_lt_one : x < 1) (hy_pos : 0 < y) :
    x ^ y < 1 := by
  simpa using Real.rpow_lt_one hx_pos hx_lt_one hy_pos

-- Common simp-normalizations for division forms
@[simp] theorem one_div_mul (x y : ℝ) : (1 / x) * y = y / x := by
  simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]

@[simp] theorem mul_one_div (x y : ℝ) : x * (1 / y) = x / y := by
  simpa [div_eq_mul_inv, one_div]

@[simp] theorem inv_pos_iff_one_div_pos {x : ℝ} : (0 < x⁻¹) ↔ (0 < 1 / x) := by
  simpa [one_div]
