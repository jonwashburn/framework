import Mathlib
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.LightLanguage.Basis.DFT8

/-!
# Canonical DFT8-backed basis map for `WTokenId` (MODEL)

This module provides a **concrete, DFT8-backed basis vector** in `ℂ⁸` for each canonical
token identity `Token.WTokenId`.

Important claim hygiene:
- This file **does not** claim the basis assignment is uniquely forced by RS.
- It is a **MODEL CHOICE** that:
  - maps the three conjugate-pair families to representative DFT modes 1,2,3, and
  - maps the self-conjugate family to mode 4,
  - and uses multiplication by `i` to distinguish the “τ₂ / imaginary” mode-4 variants.

What we *do* certify here:
- the produced basis vectors are **neutral** (mean-free over 8 ticks), because DFT modes 1..7 are neutral.

This gives a clean bridge target for later work that removes “proof-fields-as-data”
from token claims by constructing neutral bases directly from DFT8 facts.
-/

namespace IndisputableMonolith
namespace Token

open IndisputableMonolith.Water
open IndisputableMonolith.LightLanguage.Basis

namespace WTokenId

/-- MODEL: representative DFT mode for each Water WTokenMode family. -/
def dftModeOfFamily : Water.WTokenMode → Fin 8
  | .mode1_7 => 1
  | .mode2_6 => 2
  | .mode3_5 => 3
  | .mode4   => 4

lemma dftModeOfFamily_ne_zero (m : Water.WTokenMode) : dftModeOfFamily m ≠ 0 := by
  cases m <;> decide

/-- DFT8-backed neutral basis vector in `ℂ⁸` for a token id. -/
noncomputable def basisOfId (w : Token.WTokenId) : Fin 8 → ℂ :=
  let spec := WTokenId.toSpec w
  match spec.mode, spec.tau_offset with
  | .mode4, .tau2 => fun t => Complex.I * dft8_mode 4 t
  | m, _          => dft8_mode (dftModeOfFamily m)

/-- Certified: the basis is mean-free (neutral) over 8 ticks. -/
theorem basisOfId_neutral (w : Token.WTokenId) :
    Finset.univ.sum (basisOfId w) = 0 := by
  classical
  -- Reduce to cases on the Water spec fields.
  cases h : WTokenId.toSpec w with
  | mk mode phi tau hv =>
    -- Re-express `basisOfId` through the destructed spec.
    have hw : WTokenId.toSpec w = ⟨mode, phi, tau, hv⟩ := by simpa using h
    -- Split on the only special case: mode4 with tau2 (imaginary variant).
    cases mode with
    | mode4 =>
        cases tau with
        | tau0 =>
            -- basis = dft8_mode 4, which is neutral because 4 ≠ 0
            simp [basisOfId, hw, dftModeOfFamily, dft8_mode_neutral]
        | tau2 =>
            -- basis = i * dft8_mode 4; factor out i and use neutrality of mode 4
            have h4 : Finset.univ.sum (dft8_mode 4) = 0 := dft8_mode_neutral 4 (by decide)
            have hmul :
                (∑ t : Fin 8, Complex.I * dft8_mode 4 t) =
                  Complex.I * (∑ t : Fin 8, dft8_mode 4 t) := by
              -- ∑ (i * f t) = i * ∑ f t
              simpa using
                (Finset.mul_sum (s := (Finset.univ : Finset (Fin 8)))
                    (f := fun t : Fin 8 => dft8_mode 4 t) (a := Complex.I)).symm
            -- Reduce the goal to that factored form.
            simp [basisOfId, hw, hmul, h4]
    | mode1_7 =>
        simp [basisOfId, hw, dftModeOfFamily, dft8_mode_neutral]
    | mode2_6 =>
        simp [basisOfId, hw, dftModeOfFamily, dft8_mode_neutral]
    | mode3_5 =>
        simp [basisOfId, hw, dftModeOfFamily, dft8_mode_neutral]

/-- DFT8 modes have unit ℓ² norm: ∑ₜ ‖mode_k(t)‖² = 1. -/
theorem dft8_mode_normSq_sum (k : Fin 8) :
    (∑ t : Fin 8, Complex.normSq (dft8_mode k t)) = 1 := by
  -- Start from the DFT column orthonormality at (k,k).
  have h_orho : (∑ t : Fin 8, star (dft8_entry t k) * dft8_entry t k) = (1 : ℂ) := by
    simpa using (dft8_column_orthonormal k k)

  -- Convert `star z * z` into `↑(normSq z)` (commutativity + `Complex.mul_conj`).
  have h_term :
      (∑ t : Fin 8, star (dft8_entry t k) * dft8_entry t k) =
        (∑ t : Fin 8, (Complex.normSq (dft8_entry t k) : ℂ)) := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    have hz : dft8_entry t k * star (dft8_entry t k) = (Complex.normSq (dft8_entry t k) : ℂ) := by
      simpa using (Complex.mul_conj (dft8_entry t k))
    -- Swap factors to match `star z * z`.
    simpa [mul_comm] using hz

  have hC : (∑ t : Fin 8, (Complex.normSq (dft8_entry t k) : ℂ)) = (1 : ℂ) := by
    calc
      (∑ t : Fin 8, (Complex.normSq (dft8_entry t k) : ℂ))
          = (∑ t : Fin 8, star (dft8_entry t k) * dft8_entry t k) := by
              simpa using h_term.symm
      _ = 1 := h_orho

  -- Drop the coercion to ℂ (simp knows `((∑ ... ) : ℂ) = ∑ ...`).
  have hR : (∑ t : Fin 8, Complex.normSq (dft8_entry t k)) = 1 := by
    -- Coerce both sides to ℂ and use injectivity of `Complex.ofReal`.
    apply Complex.ofReal_injective
    -- `simp` rewrites the coerced sum into the sum of coerced terms.
    simpa using hC

  simpa [dft8_mode] using hR

/-- Certified: the basis has unit ℓ² norm (normalization). -/
theorem basisOfId_normalized (w : Token.WTokenId) :
    (∑ t : Fin 8, Complex.normSq (basisOfId w t)) = 1 := by
  classical
  cases h : WTokenId.toSpec w with
  | mk mode phi tau hv =>
    have hw : WTokenId.toSpec w = ⟨mode, phi, tau, hv⟩ := by simpa using h
    cases mode with
    | mode4 =>
        cases tau with
        | tau0 =>
            -- basis = dft8_mode 4
            simp [basisOfId, hw, dftModeOfFamily, dft8_mode_normSq_sum]
        | tau2 =>
            -- basis = i * dft8_mode 4 (unit-modulus scaling preserves normSq)
            have hI : Complex.normSq Complex.I = 1 := Complex.normSq_I
            simp [basisOfId, hw, dft8_mode_normSq_sum, Complex.normSq_mul, hI]
    | mode1_7 =>
        simp [basisOfId, hw, dftModeOfFamily, dft8_mode_normSq_sum]
    | mode2_6 =>
        simp [basisOfId, hw, dftModeOfFamily, dft8_mode_normSq_sum]
    | mode3_5 =>
        simp [basisOfId, hw, dftModeOfFamily, dft8_mode_normSq_sum]

/-! ## Mode Family Orthogonality -/

/-- Get the mode family of a token. -/
def modeFamily (w : Token.WTokenId) : Water.WTokenMode :=
  (WTokenId.toSpec w).mode

/-- Get the DFT mode index used by a token. -/
def dftModeIndex (w : Token.WTokenId) : Fin 8 :=
  dftModeOfFamily (modeFamily w)

/-- Inner product of two complex vectors. -/
noncomputable def innerProduct8 (v₁ v₂ : Fin 8 → ℂ) : ℂ :=
  ∑ t : Fin 8, star (v₁ t) * v₂ t

/-- DFT modes with different indices are orthogonal. -/
theorem dft8_modes_orthogonal (k₁ k₂ : Fin 8) (h : k₁ ≠ k₂) :
    innerProduct8 (dft8_mode k₁) (dft8_mode k₂) = 0 := by
  unfold innerProduct8 dft8_mode
  have := dft8_column_orthonormal k₁ k₂
  simp only [ne_eq, h, ↓reduceIte] at this
  exact this

/-- Different mode families use different DFT mode indices. -/
theorem different_family_different_mode (m₁ m₂ : Water.WTokenMode) (h : m₁ ≠ m₂) :
    dftModeOfFamily m₁ ≠ dftModeOfFamily m₂ := by
  cases m₁ <;> cases m₂ <;> simp_all [dftModeOfFamily]

/-- Helper: inner product with scaled vector on left. -/
theorem innerProduct8_scale_left (c : ℂ) (v₁ v₂ : Fin 8 → ℂ) :
    innerProduct8 (fun t => c * v₁ t) v₂ = star c * innerProduct8 v₁ v₂ := by
  unfold innerProduct8
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [star_mul]
  ring

/-- Helper: inner product with scaled vector on right. -/
theorem innerProduct8_scale_right (c : ℂ) (v₁ v₂ : Fin 8 → ℂ) :
    innerProduct8 v₁ (fun t => c * v₂ t) = c * innerProduct8 v₁ v₂ := by
  unfold innerProduct8
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- **THEOREM 1.3**: Tokens from different mode families have orthogonal bases.
    This is a key result for classification correctness. -/
theorem different_family_orthogonal (w₁ w₂ : Token.WTokenId)
    (h : modeFamily w₁ ≠ modeFamily w₂) :
    innerProduct8 (basisOfId w₁) (basisOfId w₂) = 0 := by
  -- The key insight: basis vectors use different DFT modes, which are orthogonal.
  -- Even with I-scaling (for mode4 tau2), orthogonality is preserved.
  have hk_ne : dftModeIndex w₁ ≠ dftModeIndex w₂ :=
    different_family_different_mode _ _ h
  -- Get the underlying DFT mode orthogonality
  have h_dft_orth : innerProduct8 (dft8_mode (dftModeIndex w₁)) (dft8_mode (dftModeIndex w₂)) = 0 :=
    dft8_modes_orthogonal _ _ hk_ne
  -- Now show the actual bases are either the DFT modes or I * DFT modes
  -- In either case, the I factors out and 0 * anything = 0
  unfold basisOfId dftModeIndex dftModeOfFamily modeFamily at *
  cases h1 : (WTokenId.toSpec w₁) with
  | mk m1 p1 t1 hv1 =>
    cases h2 : (WTokenId.toSpec w₂) with
    | mk m2 p2 t2 hv2 =>
      simp only [h1, h2] at h hk_ne h_dft_orth ⊢
      -- Check which case we're in for each token
      cases m1 <;> cases m2 <;> try contradiction
      all_goals (
        cases t1 <;> cases t2
        all_goals (
          first
          | exact h_dft_orth
          | (simp only [innerProduct8_scale_left, innerProduct8_scale_right, h_dft_orth, mul_zero])
        )
      )

/-- Tokens from the same family with the same τ-offset have the same basis waveform. -/
theorem same_family_same_tau_same_waveform (w₁ w₂ : Token.WTokenId)
    (h_mode : modeFamily w₁ = modeFamily w₂)
    (h_tau : (WTokenId.toSpec w₁).tau_offset = (WTokenId.toSpec w₂).tau_offset) :
    basisOfId w₁ = basisOfId w₂ := by
  unfold basisOfId modeFamily at *
  cases h1 : (WTokenId.toSpec w₁) with
  | mk m1 p1 t1 hv1 =>
    cases h2 : (WTokenId.toSpec w₂) with
    | mk m2 p2 t2 hv2 =>
      simp only [h1, h2] at h_mode h_tau ⊢
      simp [h_mode, h_tau]

/-- Self inner product equals 1 (normalized). -/
theorem self_inner_product_one (w : Token.WTokenId) :
    innerProduct8 (basisOfId w) (basisOfId w) = 1 := by
  unfold innerProduct8
  have h := basisOfId_normalized w
  -- Convert normSq sum to inner product form
  have h_eq : ∀ t, star (basisOfId w t) * basisOfId w t = Complex.normSq (basisOfId w t) := by
    intro t
    rw [mul_comm]
    exact Complex.mul_conj (basisOfId w t)
  simp_rw [h_eq]
  simp only [← Complex.ofReal_sum, h, Complex.ofReal_one]

/-! ## 2.2 Cross-Token Overlap Structure -/

/-- Get the τ-offset of a token. -/
def tauOffset (w : Token.WTokenId) : Water.TauOffset :=
  (WTokenId.toSpec w).tau_offset

/-- DFT mode self inner product = 1. -/
theorem dft8_mode_self_inner (k : Fin 8) :
    innerProduct8 (dft8_mode k) (dft8_mode k) = 1 := by
  unfold innerProduct8 dft8_mode
  have h := dft8_column_orthonormal k k
  simp only [↓reduceIte] at h
  exact h

/-- **THEOREM 2.2**: Overlap structure between tokens.
    Key cases:
    - Different mode family: overlap = 0
    - Same mode family, same τ: overlap = 1
    - Mode-4 with different τ: |overlap| = 1 (phase difference) -/
theorem overlap_different_family (w₁ w₂ : Token.WTokenId)
    (h : modeFamily w₁ ≠ modeFamily w₂) :
    innerProduct8 (basisOfId w₁) (basisOfId w₂) = 0 :=
  different_family_orthogonal w₁ w₂ h

theorem overlap_same_family_same_tau (w₁ w₂ : Token.WTokenId)
    (h_fam : modeFamily w₁ = modeFamily w₂)
    (h_tau : tauOffset w₁ = tauOffset w₂) :
    innerProduct8 (basisOfId w₁) (basisOfId w₂) = 1 := by
  have h_same := same_family_same_tau_same_waveform w₁ w₂ h_fam h_tau
  rw [h_same]
  exact self_inner_product_one w₂

/-- Mode-4 tokens with different τ have unit overlap magnitude (phase-related, not orthogonal).
    The inner product is ±I (not 0), but |inner product|² = 1. -/
theorem overlap_mode4_different_tau_magnitude (w₁ w₂ : Token.WTokenId)
    (h_fam : modeFamily w₁ = modeFamily w₂)
    (h_mode4 : modeFamily w₁ = Water.WTokenMode.mode4)
    (h_tau : tauOffset w₁ ≠ tauOffset w₂) :
    Complex.normSq (innerProduct8 (basisOfId w₁) (basisOfId w₂)) = 1 := by
  classical
  -- Reduce to cases on the underlying spec.
  unfold modeFamily at h_fam h_mode4
  unfold tauOffset at h_tau
  cases h1 : WTokenId.toSpec w₁ with
  | mk m1 p1 t1 hv1 =>
    cases h2 : WTokenId.toSpec w₂ with
    | mk m2 p2 t2 hv2 =>
      -- Extract the mode/tau equalities.
      simp only [h1, h2] at h_fam h_mode4 h_tau
      -- Both must be mode4.
      subst h_mode4
      -- And since families match, m2 = mode4 as well.
      have hm2 : m2 = Water.WTokenMode.mode4 := by simpa [h_fam]
      subst hm2
      -- Now split on the τ-offsets.
      cases t1 <;> cases t2
      · -- τ0 / τ0 contradicts h_tau
        exfalso
        exact h_tau rfl
      · -- τ0 / τ2 : ⟨mode4, I·mode4⟩ = I
        have hself : innerProduct8 (dft8_mode 4) (dft8_mode 4) = 1 := dft8_mode_self_inner 4
        unfold basisOfId
        -- simplify basisOfId on both tokens
        simp [h1, h2, dftModeOfFamily] at *
        -- compute inner product via scaling
        have hinner : innerProduct8 (dft8_mode 4) (fun t => Complex.I * dft8_mode 4 t) = Complex.I := by
          calc
            innerProduct8 (dft8_mode 4) (fun t => Complex.I * dft8_mode 4 t)
                = Complex.I * innerProduct8 (dft8_mode 4) (dft8_mode 4) := by
                    simpa using innerProduct8_scale_right (c := Complex.I) (v₁ := dft8_mode 4) (v₂ := dft8_mode 4)
            _ = Complex.I := by simp [hself]
        simp [hinner, Complex.normSq_I]
      · -- τ2 / τ0 : ⟨I·mode4, mode4⟩ = -I
        have hself : innerProduct8 (dft8_mode 4) (dft8_mode 4) = 1 := dft8_mode_self_inner 4
        unfold basisOfId
        simp [h1, h2, dftModeOfFamily] at *
        have hinner : innerProduct8 (fun t => Complex.I * dft8_mode 4 t) (dft8_mode 4) = -Complex.I := by
          calc
            innerProduct8 (fun t => Complex.I * dft8_mode 4 t) (dft8_mode 4)
                = star Complex.I * innerProduct8 (dft8_mode 4) (dft8_mode 4) := by
                    simpa using innerProduct8_scale_left (c := Complex.I) (v₁ := dft8_mode 4) (v₂ := dft8_mode 4)
            _ = -Complex.I := by simp [hself]
        -- ‖-I‖² = 1
        simpa [hinner, Complex.normSq_I] using (by rfl : Complex.normSq (-Complex.I) = (1 : ℝ))
      · -- τ2 / τ2 contradicts h_tau
        exfalso
        exact h_tau rfl

/-- Summary: Overlap squared magnitude is either 0 or 1 for all token pairs.
    This is a key structural property for classification. -/
theorem overlap_normSq_zero_or_one (w₁ w₂ : Token.WTokenId) :
    Complex.normSq (innerProduct8 (basisOfId w₁) (basisOfId w₂)) = 0 ∨
    Complex.normSq (innerProduct8 (basisOfId w₁) (basisOfId w₂)) = 1 := by
  by_cases h_fam : modeFamily w₁ = modeFamily w₂
  · -- Same family
    by_cases h_tau : tauOffset w₁ = tauOffset w₂
    · -- Same tau → overlap = 1
      right
      rw [overlap_same_family_same_tau w₁ w₂ h_fam h_tau]
      simp [Complex.normSq_one]
    · -- Different tau → only possible for mode4
      by_cases h_m4 : modeFamily w₁ = Water.WTokenMode.mode4
      · right
        exact overlap_mode4_different_tau_magnitude w₁ w₂ h_fam h_m4 h_tau
      · -- Non-mode4 can't have different tau offsets (tau_valid constraint)
        exfalso
        unfold modeFamily tauOffset at *
        cases h1 : (WTokenId.toSpec w₁) with
        | mk m1 p1 t1 hv1 =>
          cases h2 : (WTokenId.toSpec w₂) with
          | mk m2 p2 t2 hv2 =>
            simp only [h1, h2] at h_fam h_tau h_m4
            subst h_fam
            -- For non-mode4, tau_valid forces tau0
            cases m1 <;> cases t1 <;> cases t2 <;> simp_all
  · -- Different family → overlap = 0
    left
    rw [overlap_different_family w₁ w₂ h_fam]
    simp [Complex.normSq_zero]

end WTokenId

end Token
end IndisputableMonolith
