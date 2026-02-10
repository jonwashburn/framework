import Mathlib
import IndisputableMonolith.Constants

open IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Constants

/-! ### Dimensionless bridge ratio K and display equalities -/

namespace RSUnits

/-- Clock-side display definition: τ_rec(display) = K · τ0. -/
@[simp] noncomputable def tau_rec_display (U : RSUnits) : ℝ := K * RSUnits.tau0 U

/-- Length-side (kinematic) display definition: λ_kin(display) = K · ℓ0. -/
@[simp] noncomputable def lambda_kin_display (U : RSUnits) : ℝ := K * RSUnits.ell0 U

/-- Clock-side ratio: τ_rec(display)/τ0 = K. -/
@[simp] lemma tau_rec_display_ratio (U : RSUnits) (hτ : U.tau0 ≠ 0) :
  (tau_rec_display U) / RSUnits.tau0 U = K := by
  simp [tau_rec_display, hτ]

/-- Length-side ratio: λ_kin(display)/ℓ0 = K. -/
@[simp] lemma lambda_kin_display_ratio (U : RSUnits) (hℓ : U.ell0 ≠ 0) :
  (lambda_kin_display U) / RSUnits.ell0 U = K := by
  simp [lambda_kin_display, hℓ]

/-- Kinematic consistency: c · τ_rec(display) = λ_kin(display). -/
lemma lambda_kin_from_tau_rec (U : RSUnits) : U.c * tau_rec_display U = lambda_kin_display U := by
  -- c·(K τ0) = K·(c τ0) = K·ℓ0
  have : U.c * U.tau0 = U.ell0 := U.c_ell0_tau0
  calc
    U.c * tau_rec_display U = U.c * (K * U.tau0) := by rw [tau_rec_display]
    _ = K * (U.c * U.tau0) := by ring
    _ = K * U.ell0 := by rw [this]
    _ = lambda_kin_display U := by rw [lambda_kin_display]

/-- Dimensionless bridge gate: the two independent displays agree at the ratio level. -/
lemma K_gate (U : RSUnits) (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = (lambda_kin_display U) / U.ell0 := by
  rw [tau_rec_display_ratio U hτ, lambda_kin_display_ratio U hℓ]

/-- Length-side display ratio equals K. -/
lemma K_eq_lambda_over_ell0 (U : RSUnits) (hℓ : U.ell0 ≠ 0) :
  (lambda_kin_display U) / U.ell0 = K :=
  lambda_kin_display_ratio U hℓ

/-- Clock-side display ratio equals K. -/
lemma K_eq_tau_over_tau0 (U : RSUnits) (hτ : U.tau0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = K :=
  tau_rec_display_ratio U hτ

/-- Canonical K-gate: both route ratios equal K. -/
theorem K_gate_eqK (U : RSUnits) (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  ((tau_rec_display U) / U.tau0 = K) ∧ ((lambda_kin_display U) / U.ell0 = K) := by
  exact ⟨tau_rec_display_ratio U hτ, lambda_kin_display_ratio U hℓ⟩

/-- Canonical K-gate (triple form): both equal K and hence equal each other. -/
theorem K_gate_triple (U : RSUnits) (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  ((tau_rec_display U) / U.tau0 = (lambda_kin_display U) / U.ell0)
  ∧ ((tau_rec_display U) / U.tau0 = K)
  ∧ ((lambda_kin_display U) / U.ell0 = K) := by
  exact ⟨K_gate U hτ hℓ, tau_rec_display_ratio U hτ, lambda_kin_display_ratio U hℓ⟩

/-- Structural speed identity from units: ℓ0/τ0 = c. -/
lemma ell0_div_tau0_eq_c (U : RSUnits) (h : U.tau0 ≠ 0) : U.ell0 / U.tau0 = U.c := by
  calc
    U.ell0 / U.tau0 = (U.c * U.tau0) / U.tau0 := by simpa [U.c_ell0_tau0]
    _ = U.c * (U.tau0 / U.tau0) := by simp [mul_div_assoc]
    _ = U.c * 1 := by simp [div_self h]
    _ = U.c := by simp

/-- Display speed equals structural speed: (λ_kin/τ_rec) = c. -/
lemma display_speed_eq_c_of_nonzero (U : RSUnits)
  (hτ : tau_rec_display U ≠ 0) : (lambda_kin_display U) / (tau_rec_display U) = U.c := by
  calc
    (lambda_kin_display U) / (tau_rec_display U)
        = (U.c * tau_rec_display U) / (tau_rec_display U) := by
              simpa [lambda_kin_from_tau_rec]
    _   = U.c * (tau_rec_display U / tau_rec_display U) := by
              simpa using (mul_div_assoc U.c (tau_rec_display U) (tau_rec_display U))
    _   = U.c * 1 := by simp [div_self hτ]
    _   = U.c := by simp

/-! Strengthen display-speed equality: remove nonzero hypothesis by proving positivity. -/
lemma tau_rec_display_pos (U : RSUnits) (h : 0 < U.tau0) : 0 < tau_rec_display U := by
  -- K > 0 and τ0 > 0 imply K * τ0 > 0
  have hK : 0 < K := K_pos
  simpa [tau_rec_display, mul_comm] using mul_pos hK h

lemma tau_rec_display_ne_zero (U : RSUnits) (h : 0 < U.tau0) : tau_rec_display U ≠ 0 := by
  exact ne_of_gt (tau_rec_display_pos U h)

lemma display_speed_eq_c (U : RSUnits) (h : 0 < U.tau0) :
  (lambda_kin_display U) / (tau_rec_display U) = RSUnits.c U := by
  have hτ : tau_rec_display U ≠ 0 := tau_rec_display_ne_zero U h
  exact display_speed_eq_c_of_nonzero U hτ

end RSUnits

end Constants
end IndisputableMonolith