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

end WTokenId

end Token
end IndisputableMonolith
