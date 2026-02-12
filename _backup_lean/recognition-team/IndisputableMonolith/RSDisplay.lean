import Mathlib
import IndisputableMonolith.Constants

/-!
RS Units Display Functions and K-Gate Theorems

This module contains the dimensionless display functions for RS units
and the fundamental K-gate theorems that establish the bridge consistency.

Note: Using axiom stubs for dependency-light extraction.
-/

namespace IndisputableMonolith.Constants.RSUnits

/-- Clock-side display definition: τ_rec(display) = K · τ0. -/
noncomputable def tau_rec_display (U : IndisputableMonolith.Constants.RSUnits) : ℝ :=
  IndisputableMonolith.Constants.K * U.tau0

/-- Length-side (kinematic) display definition: λ_kin(display) = K · ℓ0. -/
noncomputable def lambda_kin_display (U : IndisputableMonolith.Constants.RSUnits) : ℝ :=
  IndisputableMonolith.Constants.K * U.ell0

/-- Clock-side ratio: τ_rec(display)/τ0 = K. -/
@[simp] lemma tau_rec_display_ratio (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K := by
  simp [tau_rec_display, hτ]

/-- Length-side ratio: λ_kin(display)/ℓ0 = K. -/
@[simp] lemma lambda_kin_display_ratio (U : IndisputableMonolith.Constants.RSUnits)
  (hℓ : U.ell0 ≠ 0) :
  (lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K := by
  simp [lambda_kin_display, hℓ]

/-- Kinematic consistency: c · τ_rec(display) = λ_kin(display). -/
@[simp] lemma lambda_kin_from_tau_rec (U : IndisputableMonolith.Constants.RSUnits) :
  U.c * tau_rec_display U = lambda_kin_display U := by
  -- c·(K τ0) = K·(c τ0) = K·ℓ0
  dsimp [tau_rec_display, lambda_kin_display]
  calc
    U.c * (IndisputableMonolith.Constants.K * U.tau0)
        = (IndisputableMonolith.Constants.K * U.c) * U.tau0 := by ring
    _   = IndisputableMonolith.Constants.K * (U.c * U.tau0) := by ring
    _   = IndisputableMonolith.Constants.K * U.ell0 := by simpa [U.c_ell0_tau0]

/-- Dimensionless bridge gate: the two independent displays agree at the ratio level. -/
@[simp] lemma K_gate (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = (lambda_kin_display U) / U.ell0 := by
  simp [tau_rec_display_ratio U hτ, lambda_kin_display_ratio U hℓ]

/-- Length-side display ratio equals K. -/
@[simp] lemma K_eq_lambda_over_ell0 (U : IndisputableMonolith.Constants.RSUnits)
  (hℓ : U.ell0 ≠ 0) :
  (lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K :=
  lambda_kin_display_ratio U hℓ

/-- Clock-side display ratio equals K. -/
@[simp] lemma K_eq_tau_over_tau0 (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K :=
  tau_rec_display_ratio U hτ

/-- Canonical K-gate: both route ratios equal K. -/
@[simp] theorem K_gate_eqK (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  ((tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K) ∧
  ((lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K) := by
  exact And.intro (tau_rec_display_ratio U hτ) (lambda_kin_display_ratio U hℓ)

/-- Canonical K-gate (triple form): both equal K and hence equal each other. -/
@[simp] theorem K_gate_triple (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  ((tau_rec_display U) / U.tau0 = (lambda_kin_display U) / U.ell0)
  ∧ ((tau_rec_display U) / U.tau0 = IndisputableMonolith.Constants.K)
  ∧ ((lambda_kin_display U) / U.ell0 = IndisputableMonolith.Constants.K) := by
  refine And.intro ?hEq (And.intro ?hTau ?hLambda)
  · exact K_gate U hτ hℓ
  · exact tau_rec_display_ratio U hτ
  · exact lambda_kin_display_ratio U hℓ

/-- Structural speed identity from units: ℓ0/τ0 = c. -/
@[simp] lemma ell0_div_tau0_eq_c (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : U.tau0 ≠ 0) :
  U.ell0 / U.tau0 = U.c := by
  calc
    U.ell0 / U.tau0 = (U.c * U.tau0) / U.tau0 := by simpa [U.c_ell0_tau0]
    _ = U.c * (U.tau0 / U.tau0) := by
          have := (mul_div_assoc U.c U.tau0 U.tau0)
          simpa using this
    _ = U.c * 1 := by simp [div_self hτ]
    _ = U.c := by simp

/-- Display speed equals structural speed: (λ_kin/τ_rec) = c. -/
@[simp] lemma display_speed_eq_c_of_nonzero (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : tau_rec_display U ≠ 0) : (lambda_kin_display U) / (tau_rec_display U) = U.c := by
  -- Direct field-level rewrite using the identity from `lambda_kin_from_tau_rec`
  have hLam : lambda_kin_display U = U.c * tau_rec_display U := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (lambda_kin_from_tau_rec U).symm
  have hτ' : tau_rec_display U ≠ 0 := hτ
  -- (U.c * τ) / τ = U.c
  have hdiv : (tau_rec_display U) / (tau_rec_display U) = 1 := by
    -- Avoid `div_self` recursion; use the field inverse characterization
    have : (tau_rec_display U) * (1 / tau_rec_display U) = 1 := by
      field_simp [hτ']
    -- rewrite back to division
    simpa [div_eq_mul_inv] using this
  calc
    (lambda_kin_display U) / (tau_rec_display U)
        = (U.c * tau_rec_display U) / (tau_rec_display U) := by simpa [hLam]
    _   = U.c * ((tau_rec_display U) / (tau_rec_display U)) := by
          ring
    _   = U.c * 1 := by simpa [hdiv]
    _   = U.c := by ring

/-- Strengthen display-speed equality: remove nonzero hypothesis by proving positivity. -/
lemma tau_rec_display_pos (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : 0 < U.tau0) : 0 < tau_rec_display U := by
  have hK : 0 < IndisputableMonolith.Constants.K := IndisputableMonolith.Constants.K_pos
  simpa [tau_rec_display, mul_comm] using mul_pos hK hτ

@[simp] lemma tau_rec_display_ne_zero (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : 0 < U.tau0) :
  tau_rec_display U ≠ 0 := ne_of_gt (tau_rec_display_pos U hτ)

@[simp] lemma display_speed_eq_c (U : IndisputableMonolith.Constants.RSUnits)
  (hτ : 0 < U.tau0) :
  (lambda_kin_display U) / (tau_rec_display U) = U.c := by
  simpa using (display_speed_eq_c_of_nonzero U (tau_rec_display_ne_zero U hτ))

end IndisputableMonolith.Constants.RSUnits
