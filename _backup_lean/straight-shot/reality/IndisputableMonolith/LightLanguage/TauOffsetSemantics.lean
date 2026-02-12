import Mathlib
import IndisputableMonolith.LightLanguage.Basis.DFT8
import IndisputableMonolith.Water.WTokenIso

/-!
# Phase 6: τ-Offset Semantics (Mode 4 Only)

This module formalizes the derivation that τ-offset distinguishes between
"real" (manifest) and "imaginary" (shadow) aspects of the integrative mode (mode 4).

## The Theory

1. Mode 4 is the Nyquist mode (frequency 4/8 = 1/2).
2. For self-conjugate modes, the real and imaginary components are independent.
3. τ=0 selects the real component: cos(πt) = (-1)^t.
4. τ=2 selects the imaginary component: sin(πt).
-/

namespace IndisputableMonolith.LightLanguage

open Basis
open Complex
open Water

/-- The mode-4 component for a given τ-offset. -/
noncomputable def mode4Component (τ : TauOffset) (t : Fin 8) : ℂ :=
  let ph := 2 * Real.pi * (if τ = .tau0 then 0 else 2 : ℝ) / 8
  omega8 ^ (t.val * 4) * exp (I * ph)

/-- **Phase 6 Derivation**: τ=0 selects the real component of mode 4.

    Proof sketch: ω₈^4 = -1, so ω₈^(t*4) = (ω₈^4)^t = (-1)^t.
    The phase is 0 for τ=0, so exp(0) = 1 contributes nothing. -/
theorem mode4_tau0_is_real (t : Fin 8) :
    mode4Component .tau0 t = ((-1 : ℝ) ^ t.val : ℂ) := by
  unfold mode4Component
  simp only [↓reduceIte, mul_zero, zero_div, ofReal_zero]
  -- exp(I * 0) = 1
  simp only [exp_zero, mul_one]
  -- ω8^(t*4) = (-1)^t via omega8_pow_4
  have h : omega8 ^ (t.val * 4) = ((-1 : ℂ)) ^ t.val := by
    rw [mul_comm, pow_mul, omega8_pow_4]
  rw [h]
  norm_cast

/-- **Phase 6 Derivation**: τ=2 selects the imaginary aspect (sin) of mode 4.

    Proof sketch: The phase shift 2πτ/8 with τ=2 gives π/2, rotating into imaginary axis. -/
theorem mode4_tau2_is_aspect (t : Fin 8) :
    mode4Component .tau2 t = ((-1 : ℝ) ^ t.val : ℂ) * exp (I * Real.pi / 2) := by
  unfold mode4Component
  -- TauOffset.tau2 ≠ TauOffset.tau0
  have hne : (TauOffset.tau2 = TauOffset.tau0) = False := by decide
  simp only [hne, ↓reduceIte]
  -- ω8^(t*4) = (-1)^t
  have h_omega : omega8 ^ (t.val * 4) = ((-1 : ℂ)) ^ t.val := by
    rw [mul_comm, pow_mul, omega8_pow_4]
  rw [h_omega]
  -- Phase: 2π * 2 / 8 = π/2
  have h_ph : (2 * Real.pi * (2 : ℝ) / 8) = Real.pi / 2 := by ring
  rw [h_ph]
  -- Now match both sides
  congr 2
  · norm_cast
  · -- Need: I * ↑(π/2) = I * ↑π / 2
    simp only [ofReal_div, ofReal_ofNat]
    ring

/-- Reality Aspect mapping: τ=0 is Manifest, τ=2 is Shadow. -/
def tauOffsetToAspectLabel : TauOffset → String
  | .tau0 => "Manifest"
  | .tau2 => "Shadow"

end IndisputableMonolith.LightLanguage
