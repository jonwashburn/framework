import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.ProteinFolding.Encoding.Chemistry

/-!
# DFT-8 Transform for Sequence Analysis

This module implements the 8-point Discrete Fourier Transform aligned with
the 8-beat recognition cycle.

## Key Concepts

- **DFT-8**: 8-point transform extracting frequency content from sliding windows
- **Mode 2**: Helical periodicity signal (α-helix has ~3.6 residue period)
- **Mode 4**: Strand alternation signal (β-strand has ~2 residue period)
- **Mode Interpretation**: DFT modes map to secondary structure propensities

## Physical Motivation

The 8-point window size matches the 8-tick cycle of the recognition ledger.
This synchronization allows the DFT modes to directly correspond to the
coherence patterns that stabilize secondary structures.

-/

namespace IndisputableMonolith
namespace ProteinFolding
namespace DFT8

open Constants
open Chemistry

/-! ## Complex Number Utilities -/

/-- The 8th root of unity: ω = e^(-2πi/8) -/
noncomputable def omega : ℂ := Complex.exp (-2 * Real.pi * Complex.I / 8)

/-- ω^8 = 1 (fundamental periodicity) -/
theorem omega_pow_8 : omega ^ 8 = 1 := by
  simp only [omega]
  -- (exp x)^8 = exp(8*x)
  rw [(Complex.exp_nat_mul (-2 * (Real.pi : ℂ) * Complex.I / 8) 8).symm]
  -- simplify 8 * (…/8) = …
  have hmul : (8 : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I) / 8) = (-(2 * (Real.pi : ℂ) * Complex.I)) := by
    simpa using (mul_div_cancel₀ (-(2 * (Real.pi : ℂ) * Complex.I)) (by norm_num : (8 : ℂ) ≠ 0))
  -- rewrite the exponent using the computed simplification
  -- (the term is definitional to `8 * (-(2πi)/8)`)
  simpa [hmul] using (show Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 from by
    rw [Complex.exp_neg]
    simp [Complex.exp_two_pi_mul_I])

/-! ## DFT-8 Transform -/

/-- 8-point DFT of a signal -/
noncomputable def dft8 (x : Fin 8 → ℂ) : Fin 8 → ℂ := fun k =>
  ∑ n : Fin 8, x n * omega ^ (n.val * k.val)

/-- Inverse DFT-8 -/
noncomputable def idft8 (X : Fin 8 → ℂ) : Fin 8 → ℂ := fun n =>
  (1 / 8) * ∑ k : Fin 8, X k * (Complex.exp (2 * Real.pi * Complex.I / 8)) ^ (n.val * k.val)

/-- DFT-8 of a real-valued signal -/
noncomputable def dft8Real (x : Fin 8 → ℝ) : Fin 8 → ℂ :=
  dft8 (fun n => (x n : ℂ))

/-! ## DFT-IDFT Roundtrip Properties -/

/-- The conjugate of omega: ω* = e^(2πi/8) -/
noncomputable def omega_conj : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- Equational form of omega_conj definition for rewriting -/
@[simp]
lemma omega_conj_eq : Complex.exp (2 * Real.pi * Complex.I / 8) = omega_conj := rfl

/-- omega_conj is the inverse of omega -/
lemma omega_mul_conj : omega * omega_conj = 1 := by
  simp only [omega, omega_conj]
  rw [← Complex.exp_add]
  ring_nf
  exact Complex.exp_zero

/-- DFT at k=0 is the sum of the signal (no phase factor) -/
lemma dft8_zero (x : Fin 8 → ℂ) : dft8 x 0 = ∑ n : Fin 8, x n := by
  unfold dft8
  simp only [Fin.val_zero, mul_zero, pow_zero, mul_one]

/-- IDFT at n=0 is 1/8 times the sum of the spectrum -/
lemma idft8_zero (X : Fin 8 → ℂ) : idft8 X 0 = (1 / 8) * ∑ k : Fin 8, X k := by
  unfold idft8
  simp only [Fin.val_zero, zero_mul, pow_zero, mul_one]

/-- Orthogonality of roots of unity: ∑_n (ω_conj)^(n*0) = 8 -/
lemma omega_conj_sum_zero : ∑ n : Fin 8, omega_conj ^ (n.val * 0) = 8 := by
  simp only [mul_zero, pow_zero, Finset.sum_const, Finset.card_fin]
  norm_num

/-- ω_conj^8 = 1 (conjugate is also 8th root of unity) -/
lemma omega_conj_pow_8 : omega_conj ^ 8 = 1 := by
  simp only [omega_conj]
  rw [(Complex.exp_nat_mul (2 * (Real.pi : ℂ) * Complex.I / 8) 8).symm]
  have hmul : (8 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 8) = 2 * (Real.pi : ℂ) * Complex.I := by
    field_simp
  simp [hmul, Complex.exp_two_pi_mul_I]

/-- Orthogonality sum for roots of unity: ∑_n ω_conj^(n*k) = 8 if k=0, else 0.

    For k = 0, all terms are 1, so sum = 8.
    For k ≠ 0, this is a geometric series with ratio r = ω_conj^k where r^8 = 1 and r ≠ 1.
    The sum is (r^8 - 1)/(r - 1) = 0.

    This is the key orthogonality relation for DFT. -/
lemma orthogonality_sum (k : Fin 8) :
    ∑ n : Fin 8, omega_conj ^ (n.val * k.val) = if k.val = 0 then 8 else 0 := by
  by_cases hk : k.val = 0
  · -- k = 0: all terms are 1, sum = 8
    simp only [hk, mul_zero, pow_zero, Finset.sum_const, Finset.card_fin, ↓reduceIte]
    norm_num
  · -- k ≠ 0: geometric series sums to 0
    simp only [hk, ↓reduceIte]
    -- Let r = ω_conj^k. We have r^8 = 1 and r ≠ 1.
    set r := omega_conj ^ k.val with hr_def
    have h_r_pow_8 : r ^ 8 = 1 := by
      simp only [hr_def]
      rw [← pow_mul, mul_comm, pow_mul, omega_conj_pow_8, one_pow]
    have h_r_ne_1 : r ≠ 1 := by
      simp only [hr_def, omega_conj]
      intro h_eq
      -- exp(2πi/8)^k = 1 means exp(2πik/8) = 1, so k/8 must be an integer
      -- But 0 < k < 8, so k/8 ∈ (0,1), which has no integers
      have h_k_pos : 0 < k.val := Nat.pos_of_ne_zero hk
      have h_k_lt : k.val < 8 := k.isLt
      -- Simplify: exp(θ)^n = exp(n*θ)
      rw [← Complex.exp_nat_mul] at h_eq
      -- Now h_eq: exp(k * (2πi/8)) = 1
      -- exp(θ) = 1 iff θ = m * 2πi for some integer m
      rw [Complex.exp_eq_one_iff] at h_eq
      obtain ⟨m, hm⟩ := h_eq
      -- hm: k * (2πi/8) = m * 2πi, so k/8 = m
      have h2pi_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      -- From hm: k * (2πi/8) = m * 2πi → k/8 = m
      have h_k_div : (↑k.val / 8 : ℂ) = ↑m := by
        have h1 : ↑k.val * (2 * ↑Real.pi * Complex.I / 8) = ↑m * (2 * ↑Real.pi * Complex.I) := hm
        have h2 : (↑k.val / 8) * (2 * ↑Real.pi * Complex.I) = ↑m * (2 * ↑Real.pi * Complex.I) := by
          calc (↑k.val / 8 : ℂ) * (2 * ↑Real.pi * Complex.I)
              = ↑k.val * (2 * ↑Real.pi * Complex.I / 8) := by ring
            _ = ↑m * (2 * ↑Real.pi * Complex.I) := h1
        exact mul_right_cancel₀ h2pi_ne h2
      -- So k/8 = m. Since k ∈ {1,...,7}, we get m ∈ (0,1).
      -- For m ∈ ℤ, this is impossible.
      -- Extract: k/8 = m (as reals) from the complex equation
      have h_k_real : (k.val : ℝ) / 8 = (m : ℝ) := by
        -- h_k_div : (k.val : ℂ) / 8 = (m : ℂ)
        -- Both sides are real, so taking .re extracts the value
        have h_re : (((k.val : ℕ) : ℂ) / 8).re = (m : ℂ).re := congrArg Complex.re h_k_div
        -- LHS.re = k/8, RHS.re = m
        have h_lhs : (((k.val : ℕ) : ℂ) / 8).re = (k.val : ℝ) / 8 := by
          rw [Complex.div_re]
          simp only [Complex.natCast_re, Complex.natCast_im, Complex.normSq_ofNat]
          -- Complex.re 8 = 8, Complex.im 8 = 0
          have h8_re : (8 : ℂ).re = 8 := by norm_num
          have h8_im : (8 : ℂ).im = 0 := by norm_num
          rw [h8_re, h8_im, mul_zero]
          -- Goal: k * 8 / 64 + 0 / 64 = k / 8
          simp only [zero_div, add_zero]
          ring
        have h_rhs : (m : ℂ).re = (m : ℝ) := Complex.intCast_re m
        rw [h_lhs, h_rhs] at h_re
        exact h_re
      -- k/8 ∈ (0, 1) means m ∈ (0, 1), but m ∈ ℤ, contradiction
      have h_lo : (0 : ℝ) < k.val / 8 := div_pos (Nat.cast_pos.mpr h_k_pos) (by norm_num)
      have h_hi : (k.val : ℝ) / 8 < 1 := by
        rw [div_lt_one (by norm_num : (0 : ℝ) < 8)]
        exact Nat.cast_lt.mpr h_k_lt
      rw [h_k_real] at h_lo h_hi
      -- 0 < (m : ℝ) < 1 for m : ℤ is impossible
      have hm_pos : 0 < m := Int.cast_pos.mp h_lo
      have hm_lt : m < 1 := by
        by_contra h_ge
        push_neg at h_ge
        have : (1 : ℝ) ≤ m := by exact_mod_cast h_ge
        linarith
      omega
    -- Rewrite sum as geometric series and use formula
    have h_sum : ∑ n : Fin 8, omega_conj ^ (n.val * k.val) = ∑ n : Fin 8, r ^ n.val := by
      apply Finset.sum_congr rfl
      intro n _
      simp only [hr_def]
      rw [Nat.mul_comm, pow_mul]
    rw [h_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i)]
    rw [geom_sum_eq h_r_ne_1]
    simp only [h_r_pow_8, sub_self, zero_div]

/-- DFT of IDFT at index 0: the roundtrip preserves the DC component.

    DFT and IDFT are inverses, so dft8 (idft8 X) = X.
    At k=0, this means the DC component is preserved.

    Proof uses orthogonality of 8th roots of unity. -/
lemma dft8_idft8_zero (X : Fin 8 → ℂ) :
    dft8 (idft8 X) 0 = X 0 := by
  -- Step 1: dft8 at k=0 is the sum of the signal
  rw [dft8_zero]
  -- Step 2: Expand idft8
  unfold idft8
  -- Goal: ∑ n, (1/8) * ∑ k, X k * ω^(n*k) = X 0
  -- Step 3: Pull (1/8) out of the outer sum
  rw [← Finset.mul_sum]
  -- Goal: (1/8) * ∑ n, ∑ k, X k * ω^(n*k) = X 0
  -- Step 4: Exchange order of summation
  rw [Finset.sum_comm]
  -- Goal: (1/8) * ∑ k, ∑ n, X k * ω^(n*k) = X 0
  -- Step 5: Fold omega_conj to match the orthogonality lemma
  simp only [omega_conj_eq]
  -- Step 6: Factor X k out of inner sum
  -- The inner sum has form: ∑ n, X k * omega_conj ^ (n * k)
  -- We want to factor out X k: X k * ∑ n, omega_conj ^ (n * k)
  have h_pull : ∀ k : Fin 8, ∑ n : Fin 8, X k * omega_conj ^ (n.val * k.val) =
      X k * ∑ n : Fin 8, omega_conj ^ (n.val * k.val) := fun k => by
    rw [Finset.mul_sum]
  simp only [h_pull]
  -- Step 7: Apply orthogonality: ∑ n, ω^(n*k) = 8 if k=0, else 0
  simp only [orthogonality_sum]
  -- Goal: (1/8) * ∑ k, X k * (if k.val = 0 then 8 else 0) = X 0
  -- Simplify X k * (if k.val = 0 then 8 else 0) = if k.val = 0 then X k * 8 else 0
  simp only [mul_ite, mul_zero]
  -- Goal: (1/8) * ∑ k, (if k.val = 0 then X k * 8 else 0) = X 0
  -- Simplify the conditional sum: only k=0 contributes
  have h_sum_eq : ∑ k : Fin 8, (if k.val = 0 then X k * 8 else 0) = X 0 * 8 := by
    have : (0 : Fin 8).val = 0 := rfl
    rw [Finset.sum_eq_single 0]
    · simp [this]
    · intro k _ hk
      have hk0 : k.val ≠ 0 := Fin.val_ne_of_ne hk
      simp [hk0]
    · intro h
      exact absurd (Finset.mem_univ 0) h
  rw [h_sum_eq]
  -- Goal: (1/8) * (X 0 * 8) = X 0
  ring

/-- Linearity of DFT at k=0: DFT of sum = sum of DFTs -/
lemma dft8_add_zero (x y : Fin 8 → ℂ) :
    dft8 (fun n => x n + y n) 0 = dft8 x 0 + dft8 y 0 := by
  simp only [dft8_zero]
  rw [← Finset.sum_add_distrib]

/-! ## Amplitude and Phase Extraction -/

/-- Amplitude (magnitude) of a complex number -/
noncomputable def amplitude (z : ℂ) : ℝ := Real.sqrt (Complex.normSq z)

/-- Phase (argument) of a complex number -/
noncomputable def phase (z : ℂ) : ℝ := Complex.arg z

/-- Extract mode amplitudes from DFT -/
noncomputable def modeAmplitudes (X : Fin 8 → ℂ) : Fin 8 → ℝ := fun k =>
  amplitude (X k)

/-- Extract mode phases from DFT -/
noncomputable def modePhases (X : Fin 8 → ℂ) : Fin 8 → ℝ := fun k =>
  phase (X k)

/-- Power at each mode -/
noncomputable def modePower (X : Fin 8 → ℂ) : Fin 8 → ℝ := fun k =>
  (amplitude (X k)) ^ 2

/-! ## Parseval's Theorem for DFT8 -/

/-- Amplitude squared equals normSq -/
theorem amplitude_sq (z : ℂ) : amplitude z ^ 2 = Complex.normSq z := by
  unfold amplitude
  rw [Real.sq_sqrt (Complex.normSq_nonneg z)]

/-- star(omega_conj) = omega: conjugate of conjugate is original. -/
lemma omega_conj_star_eq_omega : star omega_conj = omega := by
  simp only [omega, omega_conj, Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
  have h8 : (starRingEnd ℂ) (8 : ℂ) = 8 := Complex.conj_ofReal 8
  have hpi : (starRingEnd ℂ) (Real.pi : ℂ) = Real.pi := Complex.conj_ofReal Real.pi
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  simp only [map_div₀, map_mul, h2, h8, hpi, hI]
  ring

/-- Orthogonality sum for omega (not omega_conj): ∑_n ω^{n*k} = 8 if k=0, else 0.

    This follows from orthogonality_sum by taking complex conjugates. -/
lemma orthogonality_sum_omega (k : Fin 8) :
    ∑ n : Fin 8, omega ^ (n.val * k.val) = if k.val = 0 then 8 else 0 := by
  -- Take star of both sides of orthogonality_sum
  have h := orthogonality_sum k
  -- star of the sum equals sum of stars
  have h_star : star (∑ n : Fin 8, omega_conj ^ (n.val * k.val)) =
                ∑ n : Fin 8, star (omega_conj ^ (n.val * k.val)) :=
    map_sum (starRingEnd ℂ) _ _
  -- star(omega_conj^m) = omega^m
  have h_pow_star : ∀ m : ℕ, star (omega_conj ^ m) = omega ^ m := fun m => by
    rw [star_pow, omega_conj_star_eq_omega]
  simp only [h_pow_star] at h_star
  -- star preserves the conditional
  by_cases hk : k.val = 0
  · simp only [hk, ↓reduceIte] at h ⊢
    simp only [mul_zero, pow_zero, Finset.sum_const, Finset.card_fin]
    norm_num
  · simp only [hk, ↓reduceIte] at h ⊢
    have h_conj_zero : star (0 : ℂ) = 0 := map_zero (starRingEnd ℂ)
    rw [h] at h_star
    rw [h_conj_zero] at h_star
    exact h_star.symm

/-- omega_conj = omega^{-1}: omega_conj is the inverse of omega. -/
lemma omega_conj_eq_omega_inv : omega_conj = omega⁻¹ := by
  have h := omega_mul_conj
  rw [mul_comm] at h
  exact (inv_eq_of_mul_eq_one_left h).symm

/-- Conjugate of omega: star(ω) = ω^{-1} = omega_conj

    Proof: ω = e^{-2πi/8}, so ω* = e^{2πi/8} = omega_conj by definition.
    This is immediate from the property that exp(conj z) = conj(exp z)
    and conj(-i) = i. -/
lemma omega_star_eq_omega_conj : star omega = omega_conj := by
  simp only [omega, omega_conj, Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  -- conj(-2πi/8) = 2πi/8 since conj(i) = -i
  -- Need to simplify: (starRingEnd ℂ) (-2 * π * I / 8) = 2 * π * I / 8
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
  have h8 : (starRingEnd ℂ) (8 : ℂ) = 8 := Complex.conj_ofReal 8
  have hpi : (starRingEnd ℂ) (Real.pi : ℂ) = Real.pi := Complex.conj_ofReal Real.pi
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := Complex.conj_I
  simp only [map_div₀, map_neg, map_mul, h2, h8, hpi, hI]
  ring

/-- star of omega power equals omega_conj power. -/
lemma star_omega_pow (n : ℕ) : star (omega ^ n) = omega_conj ^ n := by
  rw [star_pow, omega_star_eq_omega_conj]

/-- omega_conj = omega^7: The conjugate is the 7th power (since omega^8 = 1). -/
lemma omega_conj_eq_pow_7 : omega_conj = omega ^ 7 := by
  have h8 : omega ^ 8 = 1 := omega_pow_8
  have hmul := omega_mul_conj
  -- ω · ω_conj = 1 and ω^8 = 1 implies ω_conj = ω^7
  calc omega_conj = 1 * omega_conj := by ring
    _ = omega^8 * omega_conj := by rw [h8]
    _ = omega^7 * (omega * omega_conj) := by ring
    _ = omega^7 * 1 := by rw [hmul]
    _ = omega^7 := by ring

/-- Orthogonality sum for omega over k: ∑_k ω^{d*k} = 8 if d=0, else 0.
    This is the key lemma for Parseval's theorem. -/
lemma orthogonality_sum_over_k (d : Fin 8) :
    ∑ k : Fin 8, omega ^ (d.val * k.val) = if d.val = 0 then 8 else 0 := by
  -- Rewrite d * k as k * d using commutativity
  have h_comm : ∀ k : Fin 8, d.val * k.val = k.val * d.val := fun k => Nat.mul_comm _ _
  simp only [h_comm]
  exact orthogonality_sum_omega d

/-- Key modular arithmetic: (n + 7m) mod 8 ≠ 0 for distinct n, m in Fin 8.
    Since 7 ≡ -1 (mod 8), we have n + 7m ≡ n - m (mod 8).
    For n ≠ m in {0,...,7}, (n - m) mod 8 ∈ {1,...,7}. -/
lemma mod8_ne_zero_of_ne (n m : Fin 8) (h : n ≠ m) : (n.val + 7 * m.val) % 8 ≠ 0 := by
  have hn : n.val < 8 := n.isLt
  have hm : m.val < 8 := m.isLt
  intro heq
  apply h
  ext
  omega

/-- **Helper**: Orthogonality relation for the product ω^(nk) * ω_conj^(mk).

When n = m: ω^(nk) * ω_conj^(nk) = (ω * ω_conj)^(nk) = 1^(nk) = 1
When n ≠ m: The sum ∑_k ω^((n-m)k) = 0 by roots of unity orthogonality

This is the key lemma for Parseval's theorem. -/
lemma omega_product_sum (n m : Fin 8) :
    ∑ k : Fin 8, omega ^ (n.val * k.val) * omega_conj ^ (m.val * k.val) =
    if n = m then 8 else 0 := by
  by_cases h : n = m
  · -- n = m: all terms are 1
    subst h
    simp only [↓reduceIte]
    have h1 : ∀ k : Fin 8, omega ^ (n.val * k.val) * omega_conj ^ (n.val * k.val) = 1 := by
      intro k
      rw [← mul_pow, omega_mul_conj, one_pow]
    simp only [h1, Finset.sum_const, Finset.card_fin]
    norm_num
  · -- n ≠ m: sum vanishes via orthogonality
    simp only [h, ↓reduceIte]
    -- Use omega_conj = omega^7 to transform product to single power
    have h_prod : ∀ k : Fin 8, omega ^ (n.val * k.val) * omega_conj ^ (m.val * k.val) =
                               omega ^ ((n.val + 7 * m.val) * k.val) := by
      intro k
      rw [omega_conj_eq_pow_7, ← pow_mul, ← pow_add]
      congr 1
      ring
    simp_rw [h_prod]
    -- Step 1: Reduce exponent modulo 8 using ω^8 = 1
    have hd_ne : (n.val + 7 * m.val) % 8 ≠ 0 := mod8_ne_zero_of_ne n m h
    have hd_lt : (n.val + 7 * m.val) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    -- Step 2: Show ∑_k ω^((n+7m)k) = ∑_k ω^((n+7m mod 8)*k)
    have h_reduce : ∀ k : Fin 8,
        omega ^ ((n.val + 7 * m.val) * k.val) =
        omega ^ ((n.val + 7 * m.val) % 8 * k.val) := by
      intro k
      have h8 : omega ^ 8 = 1 := omega_pow_8
      -- The exponent is (n+7m)*k = (8q + r)*k = 8qk + rk where r = (n+7m) mod 8
      -- ω^(8qk + rk) = ω^(8qk) * ω^(rk) = (ω^8)^(qk) * ω^(rk) = 1 * ω^(rk) = ω^(rk)
      set total := n.val + 7 * m.val with htotal
      set q := total / 8 with hq_def
      set r := total % 8 with hr_def
      have hdiv : total = 8 * q + r := by
        have := Nat.div_add_mod total 8
        omega
      have h1 : total * k.val = (8 * q + r) * k.val := by rw [hdiv]
      have h2 : (8 * q + r) * k.val = 8 * q * k.val + r * k.val := by ring
      calc omega ^ (total * k.val)
          = omega ^ ((8 * q + r) * k.val) := by rw [h1]
        _ = omega ^ (8 * q * k.val + r * k.val) := by rw [h2]
        _ = omega ^ (8 * q * k.val) * omega ^ (r * k.val) := pow_add _ _ _
        _ = omega ^ (8 * (q * k.val)) * omega ^ (r * k.val) := by ring_nf
        _ = (omega ^ 8) ^ (q * k.val) * omega ^ (r * k.val) := by rw [pow_mul]
        _ = 1 ^ (q * k.val) * omega ^ (r * k.val) := by rw [h8]
        _ = omega ^ (r * k.val) := by simp
    simp_rw [h_reduce]
    -- Step 3: Apply orthogonality_sum_over_k (has the right multiplication order d*k)
    have h_orth := orthogonality_sum_over_k ⟨(n.val + 7 * m.val) % 8, hd_lt⟩
    simp only [Fin.val_mk, hd_ne, ↓reduceIte] at h_orth
    exact h_orth

/-- The inner sum: ∑_k (x_n ω^nk)(conj(x_m) ω_conj^mk) = x_n conj(x_m) * (8 if n=m else 0) -/
lemma dft8_inner_sum (x : Fin 8 → ℂ) (n m : Fin 8) :
    ∑ k : Fin 8, (x n * omega ^ (n.val * k.val)) * (starRingEnd ℂ (x m) * omega_conj ^ (m.val * k.val)) =
    x n * starRingEnd ℂ (x m) * (if n = m then 8 else 0) := by
  have h1 : ∀ k : Fin 8, (x n * omega ^ (n.val * k.val)) * (starRingEnd ℂ (x m) * omega_conj ^ (m.val * k.val)) =
            x n * starRingEnd ℂ (x m) * (omega ^ (n.val * k.val) * omega_conj ^ (m.val * k.val)) := by
    intro k; ring
  simp_rw [h1, ← Finset.mul_sum, omega_product_sum]

/-- The diagonal sum: ∑_n x_n * conj(x_n) * 8 = 8 * ∑_n |x_n|² -/
lemma dft8_diagonal_sum (x : Fin 8 → ℂ) :
    ∑ n : Fin 8, x n * starRingEnd ℂ (x n) * 8 = 8 * ∑ n : Fin 8, (Complex.normSq (x n) : ℂ) := by
  rw [Finset.mul_sum]
  congr 1
  ext n
  have h : (Complex.normSq (x n) : ℂ) = x n * starRingEnd ℂ (x n) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
  rw [h]; ring

/-- Helper: The DFT energy sum equals 8 times the time-domain energy.

This is the unnormalized form of Parseval: ∑_k |X_k|² = 8 ∑_n |x_n|²

The proof uses:
- `dft8_inner_sum` for ∑_k (x_n ω^nk)(conj(x_m) ω_conj^mk) = x_n conj(x_m) * 8δ_{nm}
- `dft8_diagonal_sum` for ∑_n x_n conj(x_n) * 8 = 8 ∑_n |x_n|²
- Sum swapping and real/complex coercion bookkeeping
-/
lemma dft8_energy_eq (x : Fin 8 → ℂ) :
    ∑ k : Fin 8, Complex.normSq (dft8 x k) = 8 * ∑ n : Fin 8, Complex.normSq (x n) := by
  -- 1. Convert the goal to an equality of complex numbers by injecting into ℂ
  rw [← Complex.ofReal_inj]
  push_cast
  -- 2. Expand normSq as product with conjugate: |z|² = z * conj(z)
  have h_normSq : ∀ z : ℂ, (Complex.normSq z : ℂ) = z * starRingEnd ℂ z := by
    intro z
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
  simp_rw [h_normSq]
  -- 3. Expand dft8: X_k = ∑_n x_n ω^(nk)
  simp only [dft8]
  -- 4. Distribute conjugate over the sum: conj(∑_m ...) = ∑_m conj(...)
  -- and use star_omega_pow: conj(ω^nk) = ω_conj^nk
  have h_conj_sum : ∀ k : Fin 8, starRingEnd ℂ (∑ m : Fin 8, x m * omega ^ (m.val * k.val)) =
                         ∑ m : Fin 8, starRingEnd ℂ (x m) * omega_conj ^ (m.val * k.val) := by
    intro k
    rw [map_sum]
    congr 1
    ext m
    rw [map_mul, starRingEnd_apply, starRingEnd_apply, star_omega_pow]
  simp_rw [h_conj_sum]
  -- 5. Multiply the two sums: (∑_n ...) * (∑_m ...) = ∑_n ∑_m ...
  have h_prod_sums : ∀ k : Fin 8, (∑ n : Fin 8, x n * omega ^ (n.val * k.val)) *
                         (∑ m : Fin 8, starRingEnd ℂ (x m) * omega_conj ^ (m.val * k.val)) =
                        ∑ n : Fin 8, ∑ m : Fin 8, (x n * starRingEnd ℂ (x m)) *
                                  (omega ^ (n.val * k.val) * omega_conj ^ (m.val * k.val)) := by
    intro k
    rw [Finset.sum_mul_sum]
    congr 1; ext n; congr 1; ext m; ring
  simp_rw [h_prod_sums]
  -- 6. Reorder summations: ∑_k ∑_n ∑_m = ∑_n ∑_m ∑_k
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext n; rw [Finset.sum_comm]
  -- 7. Factor out x_n * star(x_m) from the inner sum
  simp_rw [← Finset.mul_sum]
  -- 8. Apply orthogonality: ∑_k ω^nk * ω_conj^mk = if n = m then 8 else 0
  simp_rw [omega_product_sum]
  -- 9. Simplify the sum with the Kronecker delta (ite n = m 8 0)
  have h_inner_sum_ite : ∀ n : Fin 8, ∑ m : Fin 8, x n * starRingEnd ℂ (x m) * (if n = m then (8 : ℂ) else 0) =
                               x n * starRingEnd ℂ (x n) * 8 := by
    intro n
    rw [Finset.sum_eq_single n]
    · -- case m = n
      simp
    · -- case m ≠ n
      intro m _ hmn
      simp [hmn.symm]
    · -- case n ∉ univ (impossible)
      intro h; simp at h
  simp_rw [h_inner_sum_ite]
  -- 10. The RHS is 8 * ∑_n x_n * star(x_n), which is exactly 8 * ∑_n |x_n|²
  rw [Finset.mul_sum]
  congr 1
  ext n
  ring

/-- Energy equality for the conjugate DFT. -/
lemma dft8_conj_energy_eq (x : Fin 8 → ℂ) :
    ∑ k : Fin 8, Complex.normSq (∑ n : Fin 8, x n * omega_conj ^ (n.val * k.val)) = 8 * ∑ n : Fin 8, Complex.normSq (x n) := by
  -- 1. Convert the goal to an equality of complex numbers by injecting into ℂ
  rw [← Complex.ofReal_inj]
  push_cast
  -- 2. Expand normSq as product with conjugate: |z|² = z * conj(z)
  have h_normSq : ∀ z : ℂ, (Complex.normSq z : ℂ) = z * starRingEnd ℂ z := by
    intro z; rw [Complex.normSq_eq_conj_mul_self, mul_comm]
  simp_rw [h_normSq]
  -- 3. Distribute conjugate over the sum: conj(∑_m ...) = ∑_m conj(...)
  -- and use star (omega_conj ^ n) = omega ^ n
  have h_conj_sum : ∀ k : Fin 8, starRingEnd ℂ (∑ m : Fin 8, x m * omega_conj ^ (m.val * k.val)) =
                         ∑ m : Fin 8, starRingEnd ℂ (x m) * omega ^ (m.val * k.val) := by
    intro k
    rw [map_sum]
    congr 1; ext m
    rw [map_mul, starRingEnd_apply, starRingEnd_apply, star_pow, omega_conj_star_eq_omega]
  simp_rw [h_conj_sum]
  -- 4. Multiply the two sums
  have h_prod_sums : ∀ k : Fin 8, (∑ n : Fin 8, x n * omega_conj ^ (n.val * k.val)) *
                         (∑ m : Fin 8, starRingEnd ℂ (x m) * omega ^ (m.val * k.val)) =
                        ∑ n : Fin 8, ∑ m : Fin 8, (x n * starRingEnd ℂ (x m)) *
                                  (omega_conj ^ (n.val * k.val) * omega ^ (m.val * k.val)) := by
    intro k
    rw [Finset.sum_mul_sum]
    congr 1; ext n; congr 1; ext m; ring
  simp_rw [h_prod_sums]
  -- 5. Reorder summations
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext n; rw [Finset.sum_comm]
  -- 6. Factor out x_n * star(x_m)
  simp_rw [← Finset.mul_sum]
  -- 7. Apply orthogonality: ∑_k ω_conj^nk * ω^mk = if n = m then 8 else 0
  have h_orth_conj : ∀ n m : Fin 8, ∑ k : Fin 8, omega_conj ^ (n.val * k.val) * omega ^ (m.val * k.val) =
                               if n = m then (8 : ℂ) else 0 := by
    intros n m
    simp_rw [mul_comm]
    have h := omega_product_sum m n
    simp only [h, eq_comm]
  simp_rw [h_orth_conj]
  -- 8. Simplify with Kronecker delta
  have h_inner_sum_ite : ∀ n : Fin 8, ∑ m : Fin 8, x n * starRingEnd ℂ (x m) * (if n = m then (8 : ℂ) else 0) =
                               x n * starRingEnd ℂ (x n) * 8 := by
    intro n
    rw [Finset.sum_eq_single n]
    · -- case m = n
      simp
    · -- case m ≠ n
      intro m _ hmn; simp [hmn.symm]
    · -- case n ∉ univ (contradiction)
      intro h; exact absurd (Finset.mem_univ n) h
  simp_rw [h_inner_sum_ite]
  -- 9. Match RHS
  rw [Finset.mul_sum]
  congr 1; ext n; ring

/-- **THEOREM: Parseval's theorem for 8-point DFT**

Energy is conserved between domains:
    ∑_n |x_n|² = (1/8) ∑_k |X_k|²

Proof uses `omega_product_sum` orthogonality. -/
theorem parseval_dft8 (x : Fin 8 → ℂ) :
    ∑ n : Fin 8, Complex.normSq (x n) =
      (1/8 : ℝ) * ∑ k : Fin 8, Complex.normSq (dft8 x k) := by
  -- Proof outline using omega_product_sum for orthogonality:
  --
  -- ∑_k |X_k|² = ∑_k X_k * star(X_k)
  --            = ∑_k (∑_n x_n ω^(nk)) * star(∑_m x_m ω^(mk))
  --            = ∑_k (∑_n x_n ω^(nk)) * (∑_m star(x_m) ω_conj^(mk))
  --            = ∑_n ∑_m x_n * star(x_m) * (∑_k ω^(nk) * ω_conj^(mk))
  --            = ∑_n ∑_m x_n * star(x_m) * 8 * δ_{nm}  [by omega_product_sum]
  --            = 8 ∑_n x_n * star(x_n)
  --            = 8 ∑_n |x_n|²
  --
  -- Key lemmas used:
  -- - star_omega_pow: star(ω^n) = ω_conj^n
  -- - omega_product_sum: ∑_k ω^(nk) * ω_conj^(mk) = 8 if n=m, else 0
  --
  -- The algebraic manipulation involves sum reordering (Finset.sum_comm)
  -- and normSq expansion (Complex.normSq_eq_conj_mul_self).
  --
  -- The proof uses omega_product_sum for orthogonality.
  -- We show ∑_k |X_k|² = 8 ∑_n |x_n|² via:
  -- 1. Expand |X_k|² = X_k * star(X_k)
  -- 2. Expand dft8 sums and distribute star
  -- 3. Swap summation order
  -- 4. Apply omega_product_sum: ∑_k ω^(nk) * ω_conj^(mk) = 8δ_{nm}
  -- 5. Diagonal sum gives 8 ∑_n |x_n|²
  --
  -- Use the energy equality lemma
  have h := dft8_energy_eq x
  -- ∑_n |x_n|² = (1/8) * 8 * ∑_n |x_n|² = (1/8) * ∑_k |X_k|²
  linarith


/-! ## Sliding Window DFT -/

/-- Extract 8-element window from a sequence at position i -/
def extractWindow (signal : List ℝ) (i : ℕ) : Fin 8 → ℝ := fun k =>
  List.getD signal (i + k.val) 0

/-- Sliding DFT-8 across a sequence -/
noncomputable def slidingDFT8 (signal : List ℝ) : List (Fin 8 → ℂ) :=
  if signal.length < 8 then []
  else List.map (fun i => dft8Real (extractWindow signal i))
                (List.range (signal.length - 7))

/-! ## Mode Interpretation for Secondary Structure -/

/-- Mode 2 corresponds to helical periodicity (~3.6 residues/turn)

    High Mode 2 amplitude indicates helix-forming tendency -/
def mode2 : Fin 8 := ⟨2, by norm_num⟩

/-- Mode 4 corresponds to strand alternation (2-residue period)

    High Mode 4 amplitude indicates strand-forming tendency -/
def mode4 : Fin 8 := ⟨4, by norm_num⟩

/-- Mode 0 is the DC component (average) -/
def mode0 : Fin 8 := ⟨0, by norm_num⟩

/-- Helix signal strength from DFT -/
noncomputable def helixSignal (X : Fin 8 → ℂ) : ℝ :=
  Real.sqrt (modePower X mode2 / 8)

/-- Strand signal strength from DFT -/
noncomputable def strandSignal (X : Fin 8 → ℂ) : ℝ :=
  Real.sqrt (modePower X mode4 / 8)

/-- Mode 2/Mode 4 ratio for secondary structure classification

    Ratio > 1.6: predominantly α-helical
    Ratio < 1.1: predominantly β-sheet
    Otherwise: mixed α/β -/
noncomputable def m2m4Ratio (X : Fin 8 → ℂ) : ℝ :=
  let p2 := modePower X mode2
  let p4 := modePower X mode4
  if p4 > 0.001 then p2 / p4 else 10  -- Avoid division by zero

/-! ## Sector Classification -/

/-- Fold sector classification based on DFT analysis -/
inductive FoldSector
  | AlphaBundle   -- Predominantly α-helical
  | BetaSheet     -- Predominantly β-sheet
  | AlphaBeta     -- Mixed α/β
  | Disordered    -- No clear secondary structure
  deriving DecidableEq, Repr

/-- Classify fold sector from M2/M4 ratio -/
noncomputable def classifySector (X : Fin 8 → ℂ) : FoldSector :=
  let ratio := m2m4Ratio X
  let p2 := modePower X mode2
  let p4 := modePower X mode4
  if p2 + p4 < 0.1 then FoldSector.Disordered
  else if ratio > 1.6 then FoldSector.AlphaBundle
  else if ratio < 1.1 then FoldSector.BetaSheet
  else FoldSector.AlphaBeta

/-! ## Sequence-Level DFT Analysis -/

/-- Compute average DFT spectrum for a sequence channel -/
noncomputable def averageSpectrum (signal : List ℝ) : Fin 8 → ℝ := fun k =>
  let spectra := slidingDFT8 signal
  if spectra.isEmpty then 0
  else (spectra.map (fun X => amplitude (X k))).sum / spectra.length

/-- Total power at Mode 2 across sequence -/
noncomputable def totalMode2Power (signal : List ℝ) : ℝ :=
  let spectra := slidingDFT8 signal
  (spectra.map (fun X => modePower X mode2)).sum

/-- Total power at Mode 4 across sequence -/
noncomputable def totalMode4Power (signal : List ℝ) : ℝ :=
  let spectra := slidingDFT8 signal
  (spectra.map (fun X => modePower X mode4)).sum

/-- Overall sequence sector from integrated DFT analysis -/
noncomputable def sequenceSector (signal : List ℝ) : FoldSector :=
  let p2 := totalMode2Power signal
  let p4 := totalMode4Power signal
  if p2 + p4 < 0.1 then FoldSector.Disordered
  else if p4 > 0.001 ∧ p2 / p4 > 1.6 then FoldSector.AlphaBundle
  else if p2 > 0.001 ∧ p4 / p2 > 0.9 then FoldSector.BetaSheet
  else FoldSector.AlphaBeta

/-! ## Phase Coherence -/

/-- Phase difference between two positions at a given mode -/
noncomputable def phaseDiff (X_i X_j : Fin 8 → ℂ) (mode : Fin 8) : ℝ :=
  let φ_i := phase (X_i mode)
  let φ_j := phase (X_j mode)
  -- Normalize to [-π, π]
  let diff := φ_j - φ_i
  if diff > Real.pi then diff - 2 * Real.pi
  else if diff < -Real.pi then diff + 2 * Real.pi
  else diff

/-- Phase coherence score (cos of phase difference) -/
noncomputable def phaseCoherence (X_i X_j : Fin 8 → ℂ) (mode : Fin 8) : ℝ :=
  Real.cos (phaseDiff X_i X_j mode)

end DFT8
end ProteinFolding
end IndisputableMonolith
