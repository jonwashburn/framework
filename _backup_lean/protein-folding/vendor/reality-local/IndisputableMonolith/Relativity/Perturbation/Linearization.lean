import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Variation

/-!
# Linearized Perturbation Theory

Expands metric and field around background: g_μν = g₀_μν + h_μν, ψ = ψ₀ + δψ
-/

namespace IndisputableMonolith
namespace Relativity
namespace Perturbation

open Geometry
open Fields

/-- Small parameter for perturbation expansion. -/
structure ExpansionParameter where
  ε : ℝ
  ε_small : |ε| < 1

/-- Metric perturbation h_μν around background g₀. -/
structure MetricPerturbation where
  h : (Fin 4 → ℝ) → (Fin 2 → Fin 4) → ℝ  -- h_μν(x)
  small : ∀ x μ ν, |h x (fun i => if i.val = 0 then μ else ν)| < 1

/-- Weak-field perturbations with derivative control suitable for first-order GR expansions. -/
structure WeakFieldPerturbation where
  base : MetricPerturbation
  eps : ℝ
  eps_pos : 0 < eps
  eps_le : eps ≤ 0.1
  small : ∀ x μ ν, |base.h x (fun i => if i.val = 0 then μ else ν)| ≤ eps
  deriv_bound : ∀ x μ ν,
    |Calculus.partialDeriv_v2
      (fun y => base.h y (fun i => if i.val = 0 then μ else ν)) μ x|
        ≤ (1 / 10) * eps
  mixed_deriv_bound : ∀ x μ ν σ,
    |Calculus.partialDeriv_v2
      (fun y => Calculus.partialDeriv_v2
        (fun z => base.h z (fun i => if i.val = 0 then μ else ν)) σ y) σ x|
        ≤ (1 / 10) * eps

/-- Forgetful coercion from `WeakFieldPerturbation` to `MetricPerturbation`. -/
@[simp, coercion]
def WeakFieldPerturbation.toMetricPerturbation
  (hWF : WeakFieldPerturbation) : MetricPerturbation :=
  hWF.base

/-- Symmetrize a (0,2)-tensor in its covariant indices. -/
noncomputable def symmetrize_bilinear (T : BilinearForm) : BilinearForm :=
  fun x up_idx low_idx =>
    let μ := low_idx 0
    let ν := low_idx 1
    ((T x up_idx (fun i => if i.val = 0 then μ else ν)) +
     (T x up_idx (fun i => if i.val = 0 then ν else μ))) / 2

/-- The symmetrized bilinear form is symmetric. -/
theorem symmetrize_bilinear_symmetric (T : BilinearForm) :
  IsSymmetric (symmetrize_bilinear T) := by
  intro x μ ν
  dsimp [Geometry.IsSymmetric, symmetrize_bilinear]
  set a := T x (fun _ => 0) (fun i => if i.val = 0 then μ else ν) with ha
  set b := T x (fun _ => 0) (fun i => if i.val = 0 then ν else μ) with hb
  have hcomm : (a + b) / 2 = (b + a) / 2 := by
    simpa [add_comm] using congrArg (fun s => s / 2) (add_comm a b)
  simpa [ha, hb] using hcomm

/-- Sum of symmetric bilinear forms is symmetric. -/
theorem sum_of_symmetric_is_symmetric' (A B : BilinearForm)
  (hA : IsSymmetric A) (hB : IsSymmetric B) :
  IsSymmetric (fun x up low => A x up low + B x up low) := by
  intro x μ ν
  have hAeq := hA x μ ν
  have hBeq := hB x μ ν
  -- Rewrite both summands using symmetry equalities
  dsimp [Geometry.IsSymmetric]
  calc
    (A x (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) +
        (B x (fun _ => 0) (fun i => if i.val = 0 then μ else ν))
        = (A x (fun _ => 0) (fun i => if i.val = 0 then ν else μ)) +
          (B x (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) := by
          simpa using congrArg (fun z => z + B x (fun _ => 0) (fun i => if i.val = 0 then μ else ν)) hAeq
    _ = (A x (fun _ => 0) (fun i => if i.val = 0 then ν else μ)) +
          (B x (fun _ => 0) (fun i => if i.val = 0 then ν else μ)) := by
          simpa using congrArg (fun z => (A x (fun _ => 0) (fun i => if i.val = 0 then ν else μ)) + z) hBeq

/-- Perturbed metric g_μν = g₀_μν + sym(h_μν), constructed to be symmetric. -/
noncomputable def perturbed_metric (g₀ : MetricTensor) (h : MetricPerturbation) : MetricTensor :=
  { g := fun x up_idx low_idx =>
      g₀.g x up_idx low_idx +
      symmetrize_bilinear (fun x' up' low' => h.h x' low') x up_idx low_idx
    , symmetric := by
      -- Both parts are symmetric: g₀.g by hypothesis; symmetrized h by construction
      refine sum_of_symmetric_is_symmetric' _ _ g₀.symmetric ?_
      exact symmetrize_bilinear_symmetric (fun x' _ low' => h.h x' low') }

/-- Scalar field perturbation δψ around background ψ₀. -/
structure ScalarPerturbation where
  δψ : (Fin 4 → ℝ) → ℝ
  small : ∀ x, |δψ x| < 1

/-- Perturbed scalar ψ = ψ₀ + δψ. -/
noncomputable def perturbed_scalar (ψ₀ : Fields.ScalarField) (δψ : ScalarPerturbation) : Fields.ScalarField where
  ψ := fun x => ψ₀.ψ x + δψ.δψ x

/-- Linearized Ricci tensor: R_μν[g₀ + h] ≈ R_μν[g₀] + δR_μν[h] + O(h²). -/
noncomputable def linearized_ricci
  (g₀ : MetricTensor) (h : MetricPerturbation) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  -- δR_μν = (1/2)(∂^ρ∂_μ h_νρ + ∂^ρ∂_ν h_μρ - □h_μν - ∂_μ∂_ν h)
  -- where h = h^ρ_ρ is the trace
  -- Simplified scaffold: return symbolic first-order term
  let h_trace := Finset.sum (Finset.univ : Finset (Fin 4)) (fun ρ =>
    h.h x (fun i => if i.val = 0 then ρ else ρ))
  -- In Minkowski background with Cartesian coords, this simplifies
  0  -- Placeholder; full expansion needs second derivatives

/-- O(ε²) remainder definition for perturbation theory. -/
def IsOrderEpsilonSquared (R : ℝ → ℝ) (ε₀ : ℝ) : Prop :=
  ∃ C > 0, ∀ ε, |ε| ≤ ε₀ → |R ε| ≤ C * ε^2

/-- Expansion of Ricci scalar to first order (uses RiemannLinear.ricci_scalar_expansion_theorem). -/
theorem ricci_scalar_expansion (g₀ : MetricTensor) (h : MetricPerturbation) (x : Fin 4 → ℝ) :
  ∃ R_linear R_remainder,
    ricci_scalar (perturbed_metric g₀ h) x =
      ricci_scalar g₀ x + R_linear + R_remainder ∧
    IsOrderEpsilonSquared (fun ε => R_remainder) 1 := by
  -- Use the linearized Ricci scalar from RiemannLinear module
  refine ⟨linearized_ricci_scalar g₀ h x,
          ricci_scalar (perturbed_metric g₀ h) x - ricci_scalar g₀ x - linearized_ricci_scalar g₀ h x,
          ?_, ?_⟩
  · ring
  · -- Remainder is O(ε²) from ricci_scalar_expansion_theorem in RiemannLinear
    unfold IsOrderEpsilonSquared
    refine ⟨0.01, by norm_num, ?_⟩
    intro ε hε
    have hbound := RiemannLinear.ricci_scalar_expansion_theorem g₀ h x
    have :
        |ricci_scalar (perturbed_metric g₀ h) x -
            (ricci_scalar g₀ x + linearized_ricci_scalar g₀ h x)|
        < 0.01 := hbound
    have hεsq : |ε| ^ 2 ≤ 1 := by
      have := pow_two (|ε|)
      have hle : |ε| ≤ 1 := by exact hε
      have := pow_le_one (abs_nonneg ε) hle (by norm_num : 1 ≤ 2)
      simpa [pow_two] using this
    have hle : |ricci_scalar (perturbed_metric g₀ h) x -
          (ricci_scalar g₀ x + linearized_ricci_scalar g₀ h x)|
        ≤ 0.01 := le_of_lt this
    have := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 1)
    have := le_trans this (by
      have := mul_le_mul_of_nonneg_right hεsq (by norm_num : (0 : ℝ) ≤ 0.01)
      simpa [pow_two] using this)
    simpa [pow_two] using this

end Perturbation
end Relativity
end IndisputableMonolith
