import Mathlib
import IndisputableMonolith.ILG.Kernel

namespace IndisputableMonolith
namespace ILG

open Real

/-!
# Target A: Poisson-with-kernel statement

This module defines the modified Poisson equation as a Fourier-space multiplier
and proves basic stability/scaling bounds relative to standard GR.
-/

/-- The modified Poisson equation in Fourier space:
    -k² Φ(k, a) = 4πG * w(k, a) * δρ(k, a)
    We define the operator-theoretic mapping from source density to potential. -/
noncomputable def poisson_operator (P : KernelParams) (k a δρ : ℝ) : ℝ :=
  if k = 0 then 0 else -(4 * pi * kernel P k a * δρ) / k^2

/-- Predicate: Φ solves the modified Poisson equation for a given source δρ. -/
def SolvesModifiedPoisson (P : KernelParams) (k a δρ Φ : ℝ) : Prop :=
  - (k^2 * Φ) = 4 * Real.pi * kernel P k a * δρ

/-- The operator definition satisfies the predicate. -/
theorem poisson_operator_solves (P : KernelParams) (k a δρ : ℝ) (hk : k ≠ 0) :
    SolvesModifiedPoisson P k a δρ (poisson_operator P k a δρ) := by
  unfold SolvesModifiedPoisson poisson_operator
  simp [hk]
  field_simp
  ring

/-- Stability/Scaling Bound: The ILG potential Φ is strictly enhanced relative to
    the GR potential Φ_GR by exactly the kernel factor w(k, a). -/
theorem poisson_enhancement (P : KernelParams) (k a δρ : ℝ) (hk : k ≠ 0) :
    let Φ_ILG := poisson_operator P k a δρ
    let Φ_GR  := -(4 * pi * δρ) / k^2
    |Φ_ILG| = kernel P k a * |Φ_GR| := by
  unfold poisson_operator
  simp [hk]
  rw [abs_div, abs_mul, abs_neg]
  have h_k2_pos : 0 < k^2 := pow_two_pos_of_ne_zero k hk
  have h_kernel_pos : 0 < kernel P k a := kernel_pos P k a
  field_simp [h_k2_pos.ne', h_kernel_pos.ne']
  rw [abs_of_pos h_kernel_pos]
  ring

/-- Coercivity Bound: The modified potential is non-vanishing for any non-vanishing source. -/
theorem poisson_coercive (P : KernelParams) (k a δρ : ℝ) (hk : k ≠ 0) (hδρ : δρ ≠ 0) :
    poisson_operator P k a δρ ≠ 0 := by
  unfold poisson_operator
  simp [hk]
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact pi_ne_zero
      · exact (kernel_pos P k a).ne'
    · exact hδρ
  · exact pow_ne_zero 2 hk

end ILG
end IndisputableMonolith
