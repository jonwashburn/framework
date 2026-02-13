import Mathlib
import IndisputableMonolith.Relativity.Variation.Functional

/-!
# Matrix Derivatives for Functional Calculus
This module provides lemmas for the derivatives of matrix operations (det, inverse, trace)
used in General Relativity and Recognition Science.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Variation

open Matrix
open Calculus

/-- **Jacobi's Formula** (Gateaux version):
    d/dε det(A + εB) |_ε=0 = det(A) tr(A⁻¹B). -/
theorem det_deriv_gateaux {n : ℕ} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : Invertible A) :
    HasDerivAt (fun ε => (A + ε • B).det) (A.det * (A⁻¹ * B).trace) 0 := by
  -- Use det(A + εB) = det(A) det(I + εA⁻¹B)
  have h_det_mul : ∀ ε, (A + ε • B).det = A.det * (1 + ε • (A⁻¹ * B)).det := by
    intro ε
    rw [← Matrix.det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_inv_of_invertible]
  simp_rw [h_det_mul]
  apply HasDerivAt.const_mul
  let M := A⁻¹ * B
  have h_deriv_I : HasDerivAt (fun ε => (1 + ε • M).det) (M.trace) 0 := by
    -- The derivative of det(I + εM) at ε=0 is tr(M).
    -- Mathlib has Matrix.hasFDerivAt_det_one : HasFDerivAt det trace 1
    have h_diff : HasFDerivAt Matrix.det (Matrix.trace : Matrix n n ℝ →L[ℝ] ℝ) 1 :=
      Matrix.hasFDerivAt_det_one
    let f := fun ε : ℝ => (1 : Matrix n n ℝ) + ε • M
    have h_f : HasDerivAt f M 0 := by
      apply HasDerivAt.add
      · apply hasDerivAt_const
      · apply HasDerivAt.smul_const (hasDerivAt_id 0)
    exact h_diff.comp_hasDerivAt 0 h_f
  exact h_deriv_I

/-- Derivative of the inverse of the determinant:
    d/dε (1/det(A + εB)) |_ε=0 = - (tr(A⁻¹B) / det(A)). -/
theorem inv_det_deriv_gateaux {n : ℕ} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : Invertible A) :
    HasDerivAt (fun ε => (A + ε • B).det⁻¹) (- (A.det⁻¹ * (A⁻¹ * B).trace)) 0 := by
  have h_det : HasDerivAt (fun ε => (A + ε • B).det) (A.det * (A⁻¹ * B).trace) 0 :=
    det_deriv_gateaux A B hA
  -- Use the chain rule for 1/x
  have h_inv : HasDerivAt (fun x => x⁻¹) (-(A.det⁻¹ ^ 2)) A.det := by
    apply hasDerivAt_inv
    exact invertible_det hA
  have h_comp := h_inv.comp 0 h_det
  simp at h_comp
  -- Simplify the derivative: -(A.det⁻¹ ^ 2) * (A.det * tr(A⁻¹B)) = - (A.det⁻¹ * tr(A⁻¹B))
  field_simp [invertible_det hA] at h_comp
  ring_nf at h_comp
  exact h_comp

/-- Derivative of sqrt(abs(det(A + εB)⁻¹)):
    d/dε sqrt|det(A + εB)⁻¹| |_ε=0 = -1/2 * sqrt|det(A)⁻¹| * tr(A⁻¹B). -/
theorem sqrt_abs_inv_det_deriv_gateaux {n : ℕ} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : Invertible A) :
    HasDerivAt (fun ε => Real.sqrt (abs (A + ε • B).det⁻¹))
               (-(1/2 : ℝ) * Real.sqrt (abs A.det⁻¹) * (A⁻¹ * B).trace) 0 := by
  let f := fun ε => (A + ε • B).det⁻¹
  have h_f : HasDerivAt f (-(A.det⁻¹ * (A⁻¹ * B).trace)) 0 := inv_det_deriv_gateaux A B hA
  let g := fun x => Real.sqrt (abs x)
  let D := A.det⁻¹
  let tr := (A⁻¹ * B).trace
  let signD := if D > 0 then (1 : ℝ) else -1
  have h_g : HasDerivAt g (signD / (2 * Real.sqrt (abs D))) D := by
    have h_det_ne : D ≠ 0 := (invertible_det hA).ne'
    by_cases h_pos : D > 0
    · simp [h_pos, abs_of_pos h_pos, signD]
      apply HasDerivAt.sqrt (hasDerivAt_id _) h_pos
    · have h_neg : D < 0 := lt_of_le_of_ne (not_gt.mp h_pos) h_det_ne
      simp [h_neg, abs_of_neg h_neg, signD]
      have h_deriv := HasDerivAt.sqrt (hasDerivAt_id (-D)) (neg_pos.mpr h_neg)
      have h_chain := h_deriv.comp D (hasDerivAt_neg _)
      simp at h_chain
      exact h_chain
  have h_comp := h_g.comp 0 h_f
  simp at h_comp
  -- Result: (signD / (2 * sqrt|D|)) * (-D * tr)
  -- Since signD * (-D) = -|D| = - (sqrt|D|)^2,
  -- this is (-1/2) * sqrt|D| * tr.
  have h_simp : (signD / (2 * Real.sqrt (abs D))) * (- (D * tr)) = -(1/2 : ℝ) * Real.sqrt (abs D) * tr := by
    have h_abs_pos : 0 < Real.sqrt (abs D) := Real.sqrt_pos.mpr (abs_pos.mpr (invertible_det hA).ne')
    field_simp [h_abs_pos.ne']
    -- signD * (-D) = - (signD * D) = - |D|
    have h_D : signD * D = abs D := by
      unfold signD; split_ifs with h
      · exact abs_of_pos h
      · have h_neg : D < 0 := lt_of_le_of_ne (not_le.mp h) (invertible_det hA).ne'
        exact (neg_mul_comm (1 : ℝ) D).symm.trans (neg_eq_abs_of_neg h_neg).symm
    rw [mul_assoc, ← neg_mul, h_D]
    ring_nf
    have h_sqrt_sq : Real.sqrt (abs D) * Real.sqrt (abs D) = abs D := Real.mul_self_sqrt (abs_nonneg D)
    rw [h_sqrt_sq]
    ring
  rw [h_simp] at h_comp
  exact h_comp

end Variation
end Relativity
end IndisputableMonolith
