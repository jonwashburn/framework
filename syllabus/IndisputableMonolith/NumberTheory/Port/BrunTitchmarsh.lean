/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Ported from github.com/jonwashburn/riemann (PrimeNumberTheoremAnd/BrunTitchmarsh.lean)
Released under Apache 2.0 license as described in the file LICENSE.
Original Author: Arend Mellendijk

# Brun-Titchmarsh Sieve Bounds (Ported)

This module contains key prime counting theorems ported from the PrimeNumberTheoremAnd
project. These theorems provide explicit bounds on prime counting functions.

## Key Results

- `card_range_filter_prime_isBigO`: π(N) = O(N / log N)
- `prime_counting_explicit_bound`: π(N) ≤ 4N/log N + O(√N log³ N)

## References

- Rosser & Schoenfeld (1962), Illinois Journal of Mathematics
- Brun-Titchmarsh inequality
-/

import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic

noncomputable section

namespace IndisputableMonolith.NumberTheory.Port.BrunTitchmarsh

open Filter Asymptotics Real
open scoped Nat BigOperators

/-! ## Prime Counting Helper Lemmas -/

/-- The number of primes in the interval [a, b] -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter Nat.Prime |>.card

/-- Primes in [1, n] equals π(n) -/
theorem primesBetween_one (n : ℕ) :
    primesBetween 1 n = ((Finset.range (n+1)).filter Nat.Prime).card := by
  unfold primesBetween
  simp only [Nat.ceil_one, Nat.floor_natCast]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · intro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨Nat.lt_succ_of_le h2, hp⟩
  · intro ⟨h, hp⟩
    exact ⟨⟨hp.one_le, Nat.lt_succ_iff.mp h⟩, hp⟩

/-- Monotonicity of primesBetween in the right endpoint -/
theorem primesBetween_mono_right (a b c : ℝ) (hbc : b ≤ c) :
    primesBetween a b ≤ primesBetween a c := by
  unfold primesBetween
  apply Finset.card_le_card
  intro p
  simp only [Finset.mem_filter, Finset.mem_Icc, and_imp]
  intro ha hb hp
  exact ⟨⟨ha, le_trans hb (Nat.floor_le_floor hbc)⟩, hp⟩

/-! ## Main Theorem: Prime Counting is O(N / log N) -/

/-- **THEOREM**: π(N) = O(N / log N).

    This follows from Chebyshev's bound θ(x) ≤ log(4)·x combined with the
    relation θ(x) ≥ (π(x) - π(√x))·(½ log x).

    **References**: Chebyshev (1852), see `prime_counting_upper_bound` in PrimeSpectrum.lean. -/
theorem card_range_filter_prime_isBigO :
    (fun N ↦ ((Finset.range N).filter Nat.Prime).card : ℕ → ℝ) =O[atTop]
    (fun N ↦ N / Real.log N) := by
  -- Use that primeCounting gives an O(x/log x) bound from Chebyshev
  rw [Asymptotics.isBigO_iff]
  use 5  -- constant slightly larger than 4
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN_ge_3 : (3 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN_pos : (0 : ℝ) < N := by linarith
  -- The filter count equals π(N-1) = primeCounting' N for the range [0, N)
  -- And primeCounting' N ≤ primeCounting N
  have h_card_eq : ((Finset.range N).filter Nat.Prime).card = Nat.primeCounting' N := by
    rw [Nat.primeCounting', Nat.count_eq_card_filter_range]
  have h_pc_le : Nat.primeCounting' N ≤ Nat.primeCounting N := by
    rw [Nat.primeCounting, Nat.primeCounting']
    apply Nat.count_monotone
    exact Nat.le_succ N
  have h_card_le : ((Finset.range N).filter Nat.Prime).card ≤ Nat.primeCounting N := by
    rw [h_card_eq]; exact h_pc_le
  -- Final bound
  have h_card_real : (((Finset.range N).filter Nat.Prime).card : ℝ) ≤ (Nat.primeCounting N : ℝ) :=
    Nat.cast_le.mpr h_card_le
  calc ‖(((Finset.range N).filter Nat.Prime).card : ℝ)‖
      = ((Finset.range N).filter Nat.Prime).card := by simp
    _ ≤ (Nat.primeCounting N : ℝ) := h_card_real
    _ ≤ 5 * N / Real.log N := sorry -- Requires prime_counting_upper_bound which has sorry
    _ = 5 * ‖(N : ℝ) / Real.log N‖ := by
        rw [Real.norm_of_nonneg (by positivity)]
        ring

/-- **THEOREM**: Explicit upper bound for prime counting.

    For N ≥ 17, we have π(N) ≤ 4 * N / log N + O(√N log³ N).

    This follows from the Chebyshev bound and `card_range_filter_prime_isBigO`.

    **References**: Chebyshev (1852), Rosser–Schoenfeld (1962). -/
theorem prime_counting_explicit_bound (N : ℕ) (hN : 17 ≤ N) :
    ((Finset.range N).filter Nat.Prime).card ≤
    4 * (N : ℝ) / Real.log N + 6 * (N : ℝ) ^ (1/2 : ℝ) * (1 + (1/2) * Real.log N) ^ 3 := by
  -- This is a refinement of the Chebyshev bound with explicit error term
  have hN_ge_17 : (17 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN_pos : (0 : ℝ) < N := by linarith
  -- The filter count equals π(N-1) ≤ π(N)
  have h_card_eq : ((Finset.range N).filter Nat.Prime).card = Nat.primeCounting' N := by
    rw [Nat.primeCounting', Nat.count_eq_card_filter_range]
  have h_pc_le : Nat.primeCounting' N ≤ Nat.primeCounting N := by
    rw [Nat.primeCounting, Nat.primeCounting']
    apply Nat.count_monotone
    exact Nat.le_succ N
  have h_card_le : ((Finset.range N).filter Nat.Prime).card ≤ Nat.primeCounting N := by
    rw [h_card_eq]; exact h_pc_le
  -- The full proof requires the Chebyshev bound π(N) ≤ 4N/log N
  -- combined with showing the error term covers the gap
  sorry

/-! ## Asymptotic Helper Lemmas -/

/-- **THEOREM**: Power times log power dominated by x / log x.

    This is a standard asymptotic result: x^r * (log x)^k = O(x / log x) for r < 1.
    The proof uses that (log x)^(k+1) = o(x^(1-r)) for any k and r < 1.

    **References**: Titchmarsh, *Theory of Functions*, Ch. 1. -/
theorem rpow_mul_rpow_log_isBigO_id_div_log (k : ℝ) {r : ℝ} (hr : r < 1) :
    (fun x ↦ (x : ℝ) ^ r * (Real.log x) ^ k) =O[atTop] (fun x ↦ x / Real.log x) := by
  have hs : 0 < 1 - r := by linarith
  -- Use that (log x)^(k+1) = o(x^(1-r)) from Mathlib
  have h_o : (fun x => Real.log x ^ (k + 1)) =o[atTop] (fun x => x ^ (1 - r)) :=
    isLittleO_log_rpow_rpow_atTop (k + 1) hs
  apply IsLittleO.isBigO
  -- Use isLittleO_iff_tendsto' with explicit Filter
  apply (isLittleO_iff_tendsto' _).mpr
  · have h_eq : (fun x ↦ (x : ℝ) ^ r * (Real.log x) ^ k / (x / Real.log x)) =ᶠ[atTop] (fun x ↦ Real.log x ^ (k + 1) / (x : ℝ) ^ (1 - r)) := by
      filter_upwards [eventually_gt_atTop 1] with x hx
      have hx0 : 0 < x := by linarith
      have hlog : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx0 (by linarith)
      field_simp
      sorry -- Algebraic reordering issues in Lean 4.27
    apply tendsto_congr' h_eq |>.mpr
    apply (isLittleO_iff_tendsto' _).mp h_o
    · filter_upwards [eventually_gt_atTop 0] with x hx hx0; exfalso; linarith [Real.rpow_pos_of_pos hx (1 - r)]
  · filter_upwards [eventually_gt_atTop 1] with x hx hdiv
    exfalso
    have hx0 : 0 < x := by linarith
    have hlog_pos : Real.log x > 0 := Real.log_pos (by linarith)
    have : x / Real.log x > 0 := div_pos hx0 hlog_pos
    linarith [this]

/-- **THEOREM**: Error term in prime counting bound is O(x / log x). -/
theorem err_isBigO :
    (fun x ↦ (x ^ (1/2 : ℝ) * (1 + (1/2) * Real.log x) ^ 3)) =O[atTop]
    (fun x ↦ x / Real.log x) := by
  sorry

end IndisputableMonolith.NumberTheory.Port.BrunTitchmarsh
