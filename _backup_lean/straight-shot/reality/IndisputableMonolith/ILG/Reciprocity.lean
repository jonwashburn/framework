import Mathlib
import IndisputableMonolith.ILG.Kernel

namespace IndisputableMonolith
namespace ILG

open Real

/-- The ILG dimensionless variable X = k * tau0 / a. -/
noncomputable def X_var (k a tau0 : ℝ) : ℝ := (k * tau0) / a

/-- A function Q(a, k) satisfies X-reciprocity if there exists a function Q_tilde
    such that Q(a, k) = Q_tilde (X_var k a tau0). -/
def HasXReciprocity (Q : ℝ → ℝ → ℝ) (tau0 : ℝ) : Prop :=
  ∃ Q_tilde : ℝ → ℝ, ∀ a k, Q a k = Q_tilde (X_var k a tau0)

/-- The X-reciprocity identity: if Q depends only on X = k*tau0/a,
    then a * ∂Q/∂a = - k * ∂Q/∂k.

    This is the derivative form of ∂lnQ/∂lna = -∂lnQ/∂lnk. -/
theorem x_reciprocity_identity (tau0 : ℝ) (Q_tilde : ℝ → ℝ)
    (a k : ℝ) (ha : a ≠ 0) (hk : k ≠ 0)
    (hQ : DifferentiableAt ℝ Q_tilde (X_var k a tau0)) :
    let Q := fun (a k : ℝ) => Q_tilde (X_var k a tau0)
    a * (deriv (fun a' => Q a' k) a) = - (k * (deriv (fun k' => Q a k') k)) := by
  set X := X_var k a tau0
  let f_a := fun a' => Q_tilde (X_var k a' tau0)
  let f_k := fun k' => Q_tilde (X_var k' a tau0)

  -- Partial with respect to a
  have h_deriv_a : deriv f_a a = deriv Q_tilde X * (-(k * tau0) / a^2) := by
    rw [show f_a = Q_tilde ∘ (fun a' => (k * tau0) / a') by funext a'; rfl]
    have h_inner : DifferentiableAt ℝ (fun a' => (k * tau0) / a') a := by
      apply DifferentiableAt.const_div
      · exact differentiableAt_id'
      · exact ha
    rw [deriv_comp a hQ h_inner]
    congr
    rw [deriv_const_div (k * tau0) differentiableAt_id' ha]
    simp
    ring

  -- Partial with respect to k
  have h_deriv_k : deriv f_k k = deriv Q_tilde X * (tau0 / a) := by
    rw [show f_k = Q_tilde ∘ (fun k' => (k' * tau0) / a) by funext k'; rfl]
    have h_inner : DifferentiableAt ℝ (fun k' => (k' * tau0) / a) k := by
      apply DifferentiableAt.div_const
      apply DifferentiableAt.mul_const
      exact differentiableAt_id'
    rw [deriv_comp k hQ h_inner]
    congr
    rw [deriv_div_const]
    simp

  -- Combine
  dsimp
  rw [h_deriv_a, h_deriv_k]
  field_simp [ha, hk]
  ring

/-- The logarithmic form of the identity: ∂lnQ/∂lna = -∂lnQ/∂lnk. -/
theorem x_reciprocity_log_identity (tau0 : ℝ) (Q_tilde : ℝ → ℝ)
    (a k : ℝ) (ha : a ≠ 0) (hk : k ≠ 0) (hQpos : Q_tilde (X_var k a tau0) ≠ 0)
    (hQ : DifferentiableAt ℝ Q_tilde (X_var k a tau0)) :
    let Q := fun (a k : ℝ) => Q_tilde (X_var k a tau0)
    (a / Q a k) * (deriv (fun a' => Q a' k) a) = - ((k / Q a k) * (deriv (fun k' => Q a k') k)) := by
  have h := x_reciprocity_identity tau0 Q_tilde a k ha hk hQ
  dsimp at h |-
  field_simp [hQpos]
  linear_combination h

end ILG
end IndisputableMonolith
