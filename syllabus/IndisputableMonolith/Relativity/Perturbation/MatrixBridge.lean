import Mathlib
import IndisputableMonolith.Relativity.Geometry.MatrixBridge
import IndisputableMonolith.Relativity.Perturbation.Linearization

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry Matrix

/-- Matrix representation of the perturbed metric equals background plus the symmetrised perturbation. -/
lemma metricToMatrix_perturbed_eq
    (g₀ : Geometry.MetricTensorPlaceholder) (h : MetricPerturbation) (x : Fin 4 → ℝ) :
    Geometry.metricToMatrix (perturbed_metric g₀ h) x =
      Geometry.metricToMatrix g₀ x +
        Matrix.of fun μ ν =>
          (h.h x (fun i => if i.val = 0 then μ else ν) +
           h.h x (fun i => if i.val = 0 then ν else μ)) / 2 := by
  classical
  ext μ ν
  simp [Geometry.metricToMatrix, perturbed_metric, symmetrize_bilinear, add_comm, add_left_comm,
    add_assoc, two_mul, div_eq_mul_inv]

/-- In a weak-field perturbation, each entry of the perturbed Minkowski metric matrix is within `ε` of the background value. -/
lemma metricToMatrix_perturbed_bound
    (hWF : WeakFieldPerturbation) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    |Geometry.metricToMatrix (perturbed_metric minkowski_tensor hWF.base) x μ ν -
      Geometry.metricToMatrix minkowski_tensor x μ ν|
      ≤ hWF.eps := by
  classical
  have h_eq := metricToMatrix_perturbed_eq minkowski_tensor hWF.base x
  have h_entry :
      Geometry.metricToMatrix (perturbed_metric minkowski_tensor hWF.base) x μ ν -
        Geometry.metricToMatrix minkowski_tensor x μ ν
      = ((hWF.base.h x (fun i => if i.val = 0 then μ else ν) +
           hWF.base.h x (fun i => if i.val = 0 then ν else μ)) / 2) := by
    have := congrArg (fun M => M μ ν) h_eq
    simp [Matrix.add_apply, Geometry.metricToMatrix] at this
    simpa [Matrix.add_apply, Geometry.metricToMatrix] using this
  have hμν := hWF.small x μ ν
  have hνμ := hWF.small x ν μ
  have h_final :
      |((hWF.base.h x (fun i => if i.val = 0 then μ else ν) +
          hWF.base.h x (fun i => if i.val = 0 then ν else μ)) / 2)| ≤ hWF.eps := by
    have h_nonneg : 0 ≤ hWF.eps := le_of_lt hWF.eps_pos
    have h_sum := (abs_add _ _).trans (add_le_add hμν hνμ)
    have := (div_le_iff (show (0 : ℝ) < 2 by norm_num)).mpr
      (by simpa [two_mul] using h_sum)
    have h_eps : 1 ≤ 2 := by norm_num
    have := this.trans (by
      have := mul_le_mul_of_nonneg_right hWF.eps_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this)
    exact this
  simpa [h_entry] using h_final

/-- Linearised inverse-metric bound for weak-field perturbations of Minkowski space. -/
lemma inverse_metric_linear_bound
    (hWF : WeakFieldPerturbation) (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    let η := Geometry.minkowskiMatrix
        M := Geometry.metricToMatrix (perturbed_metric minkowski_tensor hWF.base) x
        Δ := M - η
        approx := η - η ⬝ Δ ⬝ η in
    |M⁻¹ μ ν - approx μ ν| ≤ 6 * hWF.eps ^ 2 := by
  classical
  intros η M Δ approx
  have hΔ_bound : ∀ i j, |Δ i j| ≤ hWF.eps := by
    intro i j
    have := metricToMatrix_perturbed_bound hWF x i j
    simpa [Δ, M, η] using this
  let A := η ⬝ Δ
  have hA_bound : ∀ i j, |A i j| ≤ hWF.eps := by
    intro i j
    have : A i j = (if i.val = 0 then -1 else 1) * Δ i j := by
      simp [A, η, Matrix.mul_apply, Matrix.diagonal]
    simpa [this] using hΔ_bound i j
  have hA2_bound : ∀ i j, |(A ⬝ A) i j| ≤ 4 * hWF.eps ^ 2 := by
    intro i j
    have hsum : |∑ k : Fin 4, A i k * A k j|
        ≤ ∑ k : Fin 4, |A i k * A k j| := Finset.abs_sum_le_sum_abs _ _
    have hterm : ∀ k, |A i k * A k j| ≤ hWF.eps ^ 2 := by
      intro k
      have h1 := hA_bound i k
      have h2 := hA_bound k j
      have hε_nonneg : 0 ≤ hWF.eps := le_of_lt hWF.eps_pos
      have : |A i k| * |A k j| ≤ hWF.eps * hWF.eps :=
        mul_le_mul h1 h2 (abs_nonneg _) hε_nonneg
      simpa [pow_two, sq] using this
    have := Finset.sum_le_sum hterm
    have : ∑ k : Fin 4, |A i k * A k j| ≤ 4 * hWF.eps ^ 2 := by
      simpa [Finset.card_univ, Fintype.card_fin, Nat.smul_eq_mul, bit0, one_mul, pow_two, sq]
        using Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin 4))
          (fun k _ => hterm k)
    exact hsum.trans this
  have h_series := Geometry.neumann_series_second_order A hWF.eps hWF.eps_pos hWF.eps_le hA_bound
  have h_eps_nonneg : 0 ≤ hWF.eps := le_of_lt hWF.eps_pos
  have h_diff : |((1 + A)⁻¹ - (1 - A)) μ ν|
      ≤ 20 * hWF.eps ^ 3 + 4 * hWF.eps ^ 2 :=
    (abs_add_le_abs_add_abs _ _).trans
      (add_le_add (h_series μ ν) (hA2_bound μ ν))
  have h_eta_mul :
      |M⁻¹ μ ν - approx μ ν|
        = |(((1 + A)⁻¹ - (1 - A)) ⬝ η) μ ν| := by
    have hM : M = η ⬝ (1 + A) := by
      simp [M, η, Δ, A, Matrix.mul_add, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
    have happrox : approx = (1 - A) ⬝ η := by
      simp [approx, η, Δ, A, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
    have hInv : M⁻¹ = (1 + A)⁻¹ ⬝ η := by
      have := congrArg Matrix.inv hM
      simpa [Matrix.mul_assoc] using this
    simp [hInv, happrox, Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have h_eta_diag :
      |(((1 + A)⁻¹ - (1 - A)) ⬝ η) μ ν|
        = |((1 + A)⁻¹ - (1 - A)) μ ν| := by
    have : (((1 + A)⁻¹ - (1 - A)) ⬝ η) μ ν
        = ((1 + A)⁻¹ - (1 - A)) μ ν * (if ν.val = 0 then -1 else 1) := by
      simp [Matrix.mul_apply, η, Geometry.minkowskiMatrix, Matrix.diagonal]
    simpa [this]
  have h_simplify :
      20 * hWF.eps ^ 3 + 4 * hWF.eps ^ 2 ≤ 6 * hWF.eps ^ 2 := by
    have h_small : hWF.eps ≤ 0.1 := hWF.eps_le
    have := mul_le_mul_of_nonneg_left h_small (by norm_num : (0 : ℝ) ≤ 20)
    have := mul_le_mul_of_nonneg_right this (pow_two_nonneg _)
    have := add_le_add this (le_of_eq rfl)
    simpa [pow_two, pow_three, sq, mul_comm, mul_left_comm, mul_assoc]
  have h_main : |((1 + A)⁻¹ - (1 - A)) μ ν| ≤ 6 * hWF.eps ^ 2 :=
    h_diff.trans h_simplify
  simpa [h_eta_mul, h_eta_diag] using h_main

end Perturbation
end Relativity
end IndisputableMonolith
