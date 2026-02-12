import Mathlib
import IndisputableMonolith.Relativity.Geometry.Manifold

/-!
# Tensor Structures (Spacetime-specific, Fin 4)

This module defines tensors for 4D spacetime.
We work concretely with Fin 4 to avoid dimension-polymorphism issues.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Geometry

/-- A (p,q)-tensor on 4D spacetime: p contravariant indices, q covariant indices. -/
def Tensor (p q : ℕ) :=
  (Fin 4 → ℝ) → (Fin p → Fin 4) → (Fin q → Fin 4) → ℝ

/-- A scalar field (0,0)-tensor. -/
abbrev ScalarField := (Fin 4 → ℝ) → ℝ

/-- A vector field (1,0)-tensor. -/
abbrev VectorField := Tensor 1 0

/-- A covector field (0,1)-tensor. -/
abbrev CovectorField := Tensor 0 1

/-- A (0,2)-tensor (like a metric). -/
abbrev BilinearForm := Tensor 0 2

/-- A (2,0)-tensor (like inverse metric). -/
abbrev ContravariantBilinear := Tensor 2 0

/-- Tensor symmetry for (0,2)-tensors. -/
def IsSymmetric (T : Tensor 0 2) : Prop :=
  ∀ (x : Fin 4 → ℝ) (μ ν : Fin 4),
    T x (fun (_ : Fin 0) => 0) (fun (i : Fin 2) => if i.val = 0 then μ else ν) =
    T x (fun (_ : Fin 0) => 0) (fun (i : Fin 2) => if i.val = 0 then ν else μ)

/-- Tensor antisymmetry for (0,2)-tensors. -/
def IsAntisymmetric (T : Tensor 0 2) : Prop :=
  ∀ (x : Fin 4 → ℝ) (μ ν : Fin 4),
    T x (fun (_ : Fin 0) => 0) (fun (i : Fin 2) => if i.val = 0 then μ else ν) =
   -T x (fun (_ : Fin 0) => 0) (fun (i : Fin 2) => if i.val = 0 then ν else μ)

/-- Contract upper index p with lower index q. -/
noncomputable def contract {p q : ℕ}
  (T : Tensor (p+1) (q+1)) : Tensor p q :=
  fun x up_idx low_idx =>
    Finset.sum (Finset.univ : Finset (Fin 4)) fun μ =>
      T x (Fin.cons μ up_idx) (Fin.cons μ low_idx)

/-- Tensor product of two tensors. -/
noncomputable def tensor_product {p₁ q₁ p₂ q₂ : ℕ}
  (T₁ : Tensor p₁ q₁) (T₂ : Tensor p₂ q₂) : Tensor (p₁ + p₂) (q₁ + q₂) :=
  fun x up_idx low_idx =>
    T₁ x (fun i => up_idx (Fin.castAdd p₂ i)) (fun i => low_idx (Fin.castAdd q₂ i)) *
    T₂ x (fun i => up_idx (Fin.natAdd p₁ i)) (fun i => low_idx (Fin.natAdd q₁ i))

/-- Zero tensor. -/
noncomputable def zero_tensor {p q : ℕ} : Tensor p q :=
  fun _ _ _ => 0

theorem zero_tensor_contract {p q : ℕ} :
  contract (zero_tensor : Tensor (p+1) (q+1)) = zero_tensor := by
  funext x up_idx low_idx
  simp [contract, zero_tensor]

end Geometry
end Relativity
end IndisputableMonolith
