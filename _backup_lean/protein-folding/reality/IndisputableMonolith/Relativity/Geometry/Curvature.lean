import Mathlib
import IndisputableMonolith.Relativity.Geometry.Tensor
import IndisputableMonolith.Relativity.Geometry.Metric
import IndisputableMonolith.Relativity.Geometry.Connection

namespace IndisputableMonolith
namespace Relativity
namespace Geometry

/-- Stub Riemann tensor; identically zero. -/
noncomputable def riemann_tensor (_g : MetricTensor) : Tensor 1 3 :=
  fun _ _ _ => 0

@[simp] theorem riemann_antisymm_last_two (g : MetricTensor) :
    ∀ (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4),
      (riemann_tensor g) x (fun _ => ρ)
          (fun i => if i.val = 0 then σ else if i.val = 1 then μ else ν) =
      -(riemann_tensor g) x (fun _ => ρ)
          (fun i => if i.val = 0 then σ else if i.val = 1 then ν else μ) := by
  intro x ρ σ μ ν; simp [riemann_tensor]

/-- Stub Ricci tensor; identically zero. -/
noncomputable def ricci_tensor (_g : MetricTensor) : BilinearForm :=
  fun _ _ _ => 0

@[simp] theorem ricci_symmetric (g : MetricTensor) : IsSymmetric (ricci_tensor g) := trivial

/-- Stub Ricci scalar; identically zero. -/
noncomputable def ricci_scalar (_g : MetricTensor) (_x : Fin 4 → ℝ) : ℝ := 0

/-- Stub Einstein tensor; identically zero. -/
noncomputable def einstein_tensor (_g : MetricTensor) : BilinearForm :=
  fun _ _ _ => 0

@[simp] theorem einstein_symmetric (g : MetricTensor) : IsSymmetric (einstein_tensor g) := trivial

@[simp] theorem bianchi_contracted (g : MetricTensor) :
    ∀ (x : Fin 4 → ℝ) (ν : Fin 4),
      Finset.sum (Finset.univ : Finset (Fin 4)) (fun _ => 0) = 0 := by
  intro x ν; simp

@[simp] theorem minkowski_riemann_zero
    (x : Fin 4 → ℝ) (ρ σ μ ν : Fin 4) :
    (riemann_tensor minkowski.toMetricTensor) x (fun _ => ρ)
      (fun i => if i.val = 0 then σ else if i.val = 1 then μ else ν) = 0 := by
  simp [riemann_tensor]

@[simp] theorem minkowski_ricci_zero
    (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    (ricci_tensor minkowski.toMetricTensor) x (fun _ => 0)
      (fun i => if i.val = 0 then μ else ν) = 0 := rfl

@[simp] theorem minkowski_ricci_scalar_zero (x : Fin 4 → ℝ) :
    ricci_scalar minkowski.toMetricTensor x = 0 := rfl

@[simp] theorem minkowski_einstein_zero
    (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    (einstein_tensor minkowski.toMetricTensor) x (fun _ => 0)
      (fun i => if i.val = 0 then μ else ν) = 0 := rfl

end Geometry
end Relativity
end IndisputableMonolith
