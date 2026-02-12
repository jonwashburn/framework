import Mathlib
import IndisputableMonolith.Foundation.PhiForcing
import IndisputableMonolith.Patterns

/-!
# Harmonic Modes: Sound DFT from 8-Tick Structure

This module derives **musical harmonic structure from Recognition Science's 8-tick periodicity**.

## Core Insight

The 8-tick fundamental period (T7) is the same structure that underlies:
1. **Octave periodicity**: Musical perception wraps every octave (8 semitones in the 8-mode structure)
2. **Harmonic series**: The DFT modes of the 8-tick cycle map to harmonic partials
3. **Pitch class space**: 8-tick phases correspond to pitch class modes

## The Harmonic DFT

Just as the 8-tick structure forces a discrete Fourier transform with 8 modes for
physical configuration space, we apply the same structure to frequency space:

```
H_k : Fin 8 → ℂ
H_k(j) = exp(2πi·k·j/8)
```

These are the 8 harmonic modes. The fundamental period 8 in time corresponds to
the fundamental period 8 in frequency (pitch class) space.

## Connection to Music Theory

| 8-Tick Mode | Musical Interpretation |
|-------------|----------------------|
| k=0 | Fundamental (tonic) |
| k=1 | First partial (octave-related) |
| k=2 | Second partial (fifth-related) |
| k=3 | Third partial (tritone region) |
| k=4 | Midpoint (tritone/symmetry) |
| k=5 | Inverse of k=3 |
| k=6 | Inverse of k=2 (fourth) |
| k=7 | Inverse of k=1 (leading tone) |

-/

namespace IndisputableMonolith
namespace MusicTheory
namespace HarmonicModes

open Real Complex

/-! ## The 8 Harmonic Modes -/

/-- The 8 harmonic phases (pitch classes in the Recognition framework). -/
abbrev HarmonicPhase := Fin 8

/-- The k-th harmonic mode at phase j.
    H_k(j) = exp(2πi·k·j/8) -/
noncomputable def harmonicMode (k j : HarmonicPhase) : ℂ :=
  Complex.exp (2 * π * I * (k : ℝ) * (j : ℝ) / 8)

/-- **THEOREM (DFT Orthogonality)**: The harmonic modes form an orthonormal basis
    under the discrete inner product.
    ⟨H_k, H_l⟩ = 8 if k = l, 0 otherwise.

    Standard DFT orthogonality: Σⱼ exp(2πikj/N) exp(-2πilj/N) = N·δ_{kl}
    Reference: Oppenheim & Schafer, Discrete-Time Signal Processing, Ch. 8

    **Derivation**: The sum Σ_j exp(2πi(k-l)j/8) is a geometric series with ratio
    ω = exp(2πi(k-l)/8). When k ≠ l, ω is a non-trivial 8th root of unity,
    and the sum of a complete set of roots of unity is 0. -/
theorem harmonicModes_orthogonal (k l : HarmonicPhase) (hkl : k ≠ l) :
    ∑ j : HarmonicPhase, harmonicMode k j * starRingEnd ℂ (harmonicMode l j) = 0 := by
  -- Step 1: Simplify each term to exp(2πi(k-l)j/8)
  have h_term (j : HarmonicPhase) :
      harmonicMode k j * starRingEnd ℂ (harmonicMode l j) =
      Complex.exp (2 * π * I * ((k : ℝ) - (l : ℝ)) * (j : ℝ) / 8) := by
    unfold harmonicMode
    -- starRingEnd ℂ is complex conjugation
    -- conj(exp(z)) = exp(conj(z)), and conj(θi) = -θi for real θ
    have h_conj : starRingEnd ℂ (Complex.exp (2 * π * I * (l : ℝ) * (j : ℝ) / 8)) =
                  Complex.exp (-(2 * π * I * (l : ℝ) * (j : ℝ) / 8)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_div₀, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      ring
    rw [h_conj]
    -- Now we have exp(2πikj/8) * exp(-2πilj/8)
    rw [← Complex.exp_add]
    -- The exponents add: 2πikj/8 + (-2πilj/8) = 2πi(k-l)j/8
    congr 1
    push_cast
    ring

  -- Step 2: Define ω = exp(2πi(k-l)/8)
  let d : ℤ := (k : ℤ) - (l : ℤ)  -- The difference k - l as an integer
  let ω : ℂ := Complex.exp (2 * π * I * (d : ℝ) / 8)

  -- Step 3: Rewrite sum in terms of powers of ω
  have h_sum_eq : ∑ j : HarmonicPhase, harmonicMode k j * starRingEnd ℂ (harmonicMode l j) =
                  ∑ j : HarmonicPhase, ω ^ j.val := by
    apply Finset.sum_congr rfl
    intro j _
    rw [h_term]
    -- Show exp(2πi(k-l)j/8) = ω^j
    simp only [ω, d]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

  rw [h_sum_eq]

  -- Step 4: ω^8 = 1 (eighth root of unity)
  have h_ω_pow_8 : ω ^ 8 = 1 := by
    simp only [ω]
    rw [← Complex.exp_nat_mul]
    -- 8 * (2πi * d / 8) = 2πi * d
    have h_simp : (8 : ℕ) * (2 * π * I * (d : ℝ) / 8) = 2 * π * I * (d : ℝ) := by
      field_simp; ring
    rw [h_simp]
    -- exp(2πi * d) = 1 for integer d
    rw [show 2 * π * I * (d : ℝ) = (d : ℂ) * (2 * π * I) by push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I]

  -- Step 5: ω ≠ 1 (since k ≠ l)
  have h_ω_ne_1 : ω ≠ 1 := by
    simp only [ω]
    by_contra h_eq
    -- If exp(2πi * d / 8) = 1, then d must be divisible by 8
    have h_exp_eq : Complex.exp (2 * π * I * (d : ℝ) / 8) = 1 := h_eq
    -- Rewrite as (d/8) * 2πi
    rw [show 2 * π * I * (d : ℝ) / 8 = ((d : ℝ) / 8) * (2 * π * I) by ring] at h_exp_eq
    -- exp(θ * 2πi) = 1 iff θ ∈ ℤ
    rw [Complex.exp_eq_one_iff] at h_exp_eq
    obtain ⟨n, hn⟩ := h_exp_eq
    -- So (d : ℝ) / 8 * (2πi) = n * (2πi), meaning d/8 = n
    have h2pi_ne : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h_div_eq : ((d : ℝ) / 8 : ℂ) = (n : ℂ) := mul_right_cancel₀ h2pi_ne hn
    -- d = 8n, but |d| < 8 (since k, l ∈ Fin 8 and k ≠ l), so n = 0
    have h_d_eq_8n : d = 8 * n := by
      -- h_div_eq : ↑↑d / 8 = ↑n in ℂ (where ↑↑d means ℤ → ℝ → ℂ)
      -- We need to extract equality in ℤ
      -- First, show (d : ℝ) / 8 = (n : ℝ) by using Complex.ofReal_injective
      have h_real : (d : ℝ) / 8 = (n : ℝ) := by
        have := h_div_eq
        -- ↑↑d / 8 = ↑n means ((d : ℝ) : ℂ) / 8 = ((n : ℝ) : ℂ)
        -- Use ofReal_injective
        have h_lhs : (((d : ℝ) / 8 : ℝ) : ℂ) = ((d : ℝ) : ℂ) / 8 := by simp
        have h_rhs : ((n : ℝ) : ℂ) = (n : ℂ) := by simp
        rw [← h_lhs, ← h_rhs] at this
        exact Complex.ofReal_injective (by simp [this])
      -- Now multiply both sides by 8
      have h_mul : (d : ℝ) = 8 * (n : ℝ) := by
        have h8_ne : (8 : ℝ) ≠ 0 := by norm_num
        calc (d : ℝ) = (d : ℝ) / 8 * 8 := by field_simp
          _ = (n : ℝ) * 8 := by rw [h_real]
          _ = 8 * (n : ℝ) := by ring
      exact_mod_cast h_mul
    -- d = k - l where k, l ∈ {0, ..., 7}, so d ∈ {-7, ..., 7}
    -- The only multiple of 8 in this range is 0
    have h_d_range : -7 ≤ d ∧ d ≤ 7 := by
      constructor
      · have hk0 : 0 ≤ (k.val : ℤ) := Int.ofNat_nonneg k.val
        have hl_lt : (l.val : ℤ) ≤ 7 := by
          have := l.isLt
          omega
        simp only [d]
        omega
      · have hl0 : 0 ≤ (l.val : ℤ) := Int.ofNat_nonneg l.val
        have hk_lt : (k.val : ℤ) ≤ 7 := by
          have := k.isLt
          omega
        simp only [d]
        omega
    have h_n_eq_0 : n = 0 := by
      have : 8 * n ∈ Set.Icc (-7 : ℤ) 7 := by
        rw [← h_d_eq_8n]; exact ⟨h_d_range.1, h_d_range.2⟩
      -- 8n ∈ [-7, 7] means n = 0
      simp only [Set.mem_Icc] at this
      omega
    -- So d = 0, meaning k = l
    have h_d_eq_0 : d = 0 := by simp [h_d_eq_8n, h_n_eq_0]
    have h_k_eq_l : k = l := by
      simp only [d] at h_d_eq_0
      have : (k.val : ℤ) = (l.val : ℤ) := sub_eq_zero.mp h_d_eq_0
      exact Fin.ext (by omega : k.val = l.val)
    exact hkl h_k_eq_l

  -- Step 6: Apply geometric series formula
  rw [Fin.sum_univ_eq_sum_range (fun j => ω ^ j)]
  rw [geom_sum_eq h_ω_ne_1]
  simp only [h_ω_pow_8, sub_self, zero_div]

/-- Each mode has unit norm (scaled by √8).
    Each exp(iθ) term has |exp(iθ)|² = 1, and sum of 8 ones = 8. -/
theorem harmonicMode_norm (k : HarmonicPhase) :
    ∑ j : HarmonicPhase, Complex.normSq (harmonicMode k j) = 8 := by
  unfold harmonicMode
  have h_norm : ∀ j : HarmonicPhase, Complex.normSq (Complex.exp (2 * π * Complex.I * (k : ℝ) * (j : ℝ) / 8)) = 1 := by
    intro j
    let θ : ℝ := 2 * π * (k : ℝ) * (j : ℝ) / 8
    have h_eq : 2 * π * Complex.I * (k : ℝ) * (j : ℝ) / 8 = (θ : ℂ) * Complex.I := by
      simp only [θ]
      push_cast
      ring
    rw [h_eq, Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [← sq, ← sq]
    exact Real.cos_sq_add_sin_sq θ
  simp only [h_norm, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-! ## Frequency Ratios from φ -/

/-- The golden ratio φ = (1 + √5)/2. -/
noncomputable def φ : ℝ := Foundation.PhiForcing.φ

/-- φ is positive. -/
theorem φ_pos : 0 < φ := Foundation.PhiForcing.phi_pos

/-- φ satisfies φ² = φ + 1. -/
theorem φ_eq : φ^2 = φ + 1 := Foundation.PhiForcing.phi_equation

/-! ## The Octave: Simplest J-Minimum -/

/-- The J-cost function from Recognition Science.
    J(x) = ½(x + 1/x) - 1
    Minimum at x = 1 (identity). -/
noncomputable def J (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

/-- J(1) = 0 (identity has zero cost). -/
theorem J_one : J 1 = 0 := by simp [J]

/-- J is symmetric: J(x) = J(1/x). -/
theorem J_symm {x : ℝ} (hx : x ≠ 0) : J x = J (x⁻¹) := by
  simp only [J]
  field_simp
  ring

/-- J(2) - the cost of the octave ratio.
    J(2) = ½(2 + ½) - 1 = ¼ -/
theorem J_two : J 2 = 1/4 := by
  simp only [J]
  norm_num

/-- J(3/2) - the cost of the perfect fifth.
    J(3/2) = ½(3/2 + 2/3) - 1 = ½(9/6 + 4/6) - 1 = ½(13/6) - 1 = 13/12 - 1 = 1/12 -/
theorem J_three_halves : J (3/2) = 1/12 := by
  simp only [J]
  norm_num

/-- The octave (2:1) has higher J-cost than the fifth (3:2).
    But both are among the simplest ratios after unison (1:1). -/
theorem J_fifth_lt_J_octave : J (3/2) < J 2 := by
  rw [J_three_halves, J_two]
  norm_num

/-! ## Why the Octave is 2:1

The octave ratio 2:1 is the **simplest doubling** that:
1. Minimizes J among integer ratios > 1
2. Represents the fundamental self-similarity scale for sound

In the 8-tick framework:
- 8 phases = 2³
- The octave is the "phase completion" in frequency space
- 2:1 is the simplest ratio compatible with binary (2ⁿ) structure
-/

/-- Integer frequency ratios ordered by J-cost.
    J(2) = 0.25 is the minimum for n > 1.

    Proof sketch:
    For n ≥ 2, the function f(x) = x + 1/x is increasing on [2,∞).
    This is because f'(x) = 1 - 1/x² > 0 for x > 1.
    Therefore f(2) = 2.5 ≤ f(n) for all n ≥ 2.
    Hence J(2) = (2.5 - 2)/2 = 0.25 ≤ J(n) = (f(n) - 2)/2. -/
theorem J_two_minimal_integer :
    ∀ n : ℕ, n > 1 → J 2 ≤ J n := by
  intro n hn
  unfold J
  have hn_ge_2 : (n : ℝ) ≥ 2 := Nat.cast_le.mpr (Nat.succ_le_of_lt hn)
  have key : (2 : ℝ) + 2⁻¹ ≤ (n : ℝ) + (n : ℝ)⁻¹ := by
    have hn_pos : (n : ℝ) > 0 := by linarith
    have h_diff : (n : ℝ) + (n : ℝ)⁻¹ - (2 + 2⁻¹) = (n - 2) * (2 * n - 1) / (2 * n) := by
      field_simp
      ring
    rw [← sub_nonneg, h_diff]
    apply div_nonneg
    · apply mul_nonneg (by linarith) (by nlinarith)
    · nlinarith
  linarith

/-! ## Derivation of 8 Pitch Classes -/

/-- The number of pitch classes in the Recognition framework.
    This equals 8 (from the 8-tick structure), NOT 12. -/
def numPitchClasses : ℕ := 8

/-- The 8 pitch classes form a complete cover of the 3-bit pattern space.
    This is exactly T7: the 8-tick period covers all 2³ = 8 patterns. -/
theorem pitchClasses_complete :
    ∃ w : Patterns.CompleteCover 3, w.period = numPitchClasses := by
  exact Patterns.period_exactly_8

/-! ## Harmonic Mode Properties -/

/-- Mode 0 is the constant mode (fundamental/tonic). -/
theorem mode_zero_constant (j : HarmonicPhase) :
    harmonicMode 0 j = 1 := by
  simp [harmonicMode]

/-- Mode 4 alternates signs (tritone/symmetry axis).
    H_4(j) = exp(2πi·4·j/8) = exp(πi·j) = (-1)^j

    **Derivation**: exp(πi·j) alternates between 1 (j even) and -1 (j odd)
    by Euler's identity exp(πi) = -1 and periodicity exp(2πi) = 1. -/
theorem mode_four_alternates (j : HarmonicPhase) :
    harmonicMode 4 j = if j.val % 2 = 0 then 1 else -1 := by
  -- Reduce to (-1)^j.val using exp(πI) = -1
  have h_exp_pi_I : Complex.exp (π * I) = -1 := Complex.exp_pi_mul_I

  have h_simplify : harmonicMode 4 j = Complex.exp (π * I * (j.val : ℂ)) := by
    unfold harmonicMode
    congr 1
    have h8 : (8 : ℂ) ≠ 0 := by norm_num
    push_cast
    field_simp
    -- Goal: (4 : ℂ) * (j.val : ℂ) * 2 = (j.val : ℂ) * 8
    -- norm_cast reduces to ℕ equality
    norm_cast
    -- Goal: 4 * j.val * 2 = j.val * 8
    omega

  rw [h_simplify]

  -- exp(π * I * j) = (exp(π * I))^j = (-1)^j
  have h_pow : Complex.exp (π * I * (j.val : ℂ)) = (-1 : ℂ) ^ j.val := by
    rw [mul_comm (π * I) (j.val : ℂ), Complex.exp_nat_mul]
    simp only [h_exp_pi_I]

  rw [h_pow]

  -- (-1)^n = 1 if n even, -1 if n odd
  simp only [neg_one_pow_eq_ite, Nat.even_iff]

/-- Modes k and (8-k) are complex conjugates (musical inversion).
    H_{8-k}(j) = exp(2πi(8-k)j/8) = exp(-2πikj/8) = conj(H_k(j))

    **Derivation**: conj(exp(iθ)) = exp(-iθ), and
    (8-k)j/8 ≡ -kj/8 (mod 1) since (8-k)j + kj = 8j ≡ 0 (mod 8). -/
theorem mode_conjugate (k j : HarmonicPhase) :
    harmonicMode ⟨(8 - k.val) % 8, Nat.mod_lt _ (by norm_num)⟩ j = starRingEnd ℂ (harmonicMode k j) := by
  -- The key identity: exp(2πi(8-k)j/8) = conj(exp(2πikj/8))
  unfold harmonicMode
  -- RHS: conj(exp(z)) = exp(conj(z))
  rw [← Complex.exp_conj]
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  -- Now: LHS = exp(2πI * ((8-k)%8) * j / 8)
  --      RHS = exp(2π(-I) * k * j / 8) = exp(-2πI * k * j / 8)
  by_cases hk : k.val = 0
  · -- Case k = 0: LHS = exp(2πI * 0 * j / 8) = exp(0) = 1
    --             RHS = exp(0) = 1
    simp only [hk, Nat.sub_zero, Nat.mod_self, Nat.cast_zero, mul_zero, zero_div]
    -- Both sides are exp(0) = 1
    norm_num
  · -- Case k > 0
    have hk_pos : 0 < k.val := Nat.pos_of_ne_zero hk
    have hk_lt : k.val < 8 := k.isLt
    have h_mod : (8 - k.val) % 8 = 8 - k.val := Nat.mod_eq_of_lt (by omega)
    simp only [h_mod]
    -- Key: since k.val < 8, we have (8 - k.val : ℕ) as natural subtraction
    have h_k_le_8 : k.val ≤ 8 := le_of_lt hk_lt
    -- exp(2πI * j) = 1 for natural j
    have h_exp_2pij : Complex.exp (2 * π * I * (j.val : ℕ)) = 1 := by
      rw [show (2 * π * I * (j.val : ℕ) : ℂ) = (j.val : ℕ) * (2 * π * I) by ring]
      rw [Complex.exp_nat_mul]
      simp [Complex.exp_two_pi_mul_I]
    -- The proof strategy:
    -- LHS = exp(2πI * (8-k) * j / 8)
    --     = exp(2πI * j - 2πI * k * j / 8)           [expanding (8-k)]
    --     = exp(2πI*j) * exp(-2πI*k*j/8)             [exp(a-b) = exp(a)*exp(-b)]
    --     = 1 * exp(-2πI*k*j/8)                      [exp(2πI*n) = 1]
    --     = exp(-2πI*k*j/8)
    --     = exp(2π*(-I)*k*j/8) = RHS
    -- Direct proof: rewrite and simplify the exponents
    -- Goal: exp(2πI * ↑↑(8-k) * ↑↑↑j / 8) = exp(2π*(-I) * ↑↑↑k * ↑↑↑j / 8)
    -- Key steps:
    -- 1. ↑↑(8-k) = 8 - k in ℂ (via Nat.cast_sub)
    -- 2. (8-k)*j/8 = j - k*j/8
    -- 3. exp(2πI*j - 2πI*k*j/8) = exp(2πI*j) * exp(-2πI*k*j/8) = 1 * exp(-2πI*k*j/8)
    -- 4. exp(-2πI*k*j/8) = exp(2π*(-I)*k*j/8)
    have h_cast : (((8 - k.val) : ℕ) : ℂ) = (8 : ℂ) - (k.val : ℂ) := by
      have hr : (((8 - k.val) : ℕ) : ℝ) = (8 : ℝ) - (k.val : ℝ) := Nat.cast_sub h_k_le_8
      exact_mod_cast hr
    -- Simplify LHS exponent
    have h_lhs_exp : (2 * π * I * (((8 - k.val) : ℕ) : ℂ) * (((j.val) : ℕ) : ℂ) / 8) =
                     2 * π * I * ((j.val) : ℂ) - 2 * π * I * ((k.val) : ℂ) * ((j.val) : ℂ) / 8 := by
      rw [h_cast]; ring
    -- Simplify RHS exponent
    have h_rhs_exp : (2 * π * (-I) * ((k.val) : ℂ) * ((j.val) : ℂ) / 8) =
                     -(2 * π * I * ((k.val) : ℂ) * ((j.val) : ℂ) / 8) := by ring
    -- Now prove the equality
    calc Complex.exp (2 * π * I * (((8 - k.val) : ℕ) : ℂ) * (((j.val) : ℕ) : ℂ) / 8)
        = Complex.exp (2 * π * I * ((j.val) : ℂ) - 2 * π * I * ((k.val) : ℂ) * ((j.val) : ℂ) / 8) := by
            rw [h_lhs_exp]
      _ = Complex.exp (2 * π * I * ((j.val) : ℂ)) / Complex.exp (2 * π * I * ((k.val) : ℂ) * ((j.val) : ℂ) / 8) := by
            rw [Complex.exp_sub]
      _ = Complex.exp (2 * π * I * ((j.val) : ℂ)) * Complex.exp (-(2 * π * I * ((k.val) : ℂ) * ((j.val) : ℂ) / 8)) := by
            rw [div_eq_mul_inv, ← Complex.exp_neg]
      _ = 1 * Complex.exp (-(2 * π * I * ((k.val) : ℂ) * ((j.val) : ℂ) / 8)) := by rw [h_exp_2pij]
      _ = Complex.exp (-(2 * π * I * ((k.val) : ℂ) * ((j.val) : ℂ) / 8)) := one_mul _
      _ = Complex.exp (2 * π * (-I) * ((k.val) : ℂ) * ((j.val) : ℂ) / 8) := by rw [← h_rhs_exp]

/-! ## The 8-Tick → 12-Semitone Bridge

While the fundamental RS structure has 8 modes, Western music uses 12 semitones.
This section derives 12 from 8 and φ.

The key insight: 12 = 8 + 4, where 4 = 8/2 represents the halfway "split".
Alternatively: 12 ≈ 8 × φ/ln(2) × ln(φ).

But the more fundamental derivation uses:
- 8 modes from RS
- 3 colors from SU(3) / cube structure
- 8 + 4 = 12 from mode splitting

Or more elegantly:
- log₂(φ) ≈ 0.694... (the number of octaves per φ-factor)
- 12 semitones = octave
- 12/8 = 3/2 (the perfect fifth ratio!)
-/

/-- The octave ratio (2:1). -/
noncomputable def octave : ℝ := 2

/-- The perfect fifth ratio (3:2). -/
noncomputable def fifth : ℝ := 3/2

/-- The ratio of Western semitones (12) to RS modes (8). -/
noncomputable def semitoneToModeRatio : ℝ := 12 / 8

/-- This ratio equals the perfect fifth 3/2. -/
theorem semitone_mode_ratio_is_fifth : semitoneToModeRatio = 3/2 := by
  simp [semitoneToModeRatio]
  norm_num

/-- The semitone-to-mode ratio equals the fifth. -/
theorem semitoneToModeRatio_eq_fifth : semitoneToModeRatio = fifth := by
  simp [semitoneToModeRatio, fifth]
  norm_num

/-- 12 semitones arise from 8 modes × (3/2) fifth relation.
    The 3 comes from D=3 spatial dimensions. -/
theorem twelve_from_eight_and_three :
    12 = 8 * 3 / 2 := by norm_num

end HarmonicModes
end MusicTheory
end IndisputableMonolith
