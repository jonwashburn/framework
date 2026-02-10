import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus

/-!
# Null Geodesics

Implements null geodesics for light propagation: dx^μ/dλ with g_μν dx^μ dx^ν = 0.
Foundation for computing gravitational lensing deflection angles and time delays.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Geodesics

open Geometry
open Calculus

/-- Null geodesic: path with zero interval (using lam for affine parameter). -/
structure NullGeodesic (g : MetricTensor) where
  path : ℝ → (Fin 4 → ℝ)  -- x^μ(lam) where lam is affine parameter
  null_condition : ∀ lam : ℝ,
    -- g_μν dx^μ/dlam dx^ν/dlam = 0
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
      Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
        g.g (path lam) (fun _ => 0) (fun i => if i.val = 0 then μ else ν) *
        (deriv (fun lam' => path lam' μ) lam) *
        (deriv (fun lam' => path lam' ν) lam))) = 0
  geodesic_equation : ∀ lam μ,
    -- d²x^μ/dlam² + Γ^μ_ρσ dx^ρ/dlam dx^σ/dlam = 0
    deriv (deriv (fun lam' => path lam' μ)) lam +
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun ρ =>
      Finset.sum (Finset.univ : Finset (Fin 4)) (fun σ =>
        (christoffel_from_metric g).Γ (path lam) μ ρ σ *
        (deriv (fun lam' => path lam' ρ) lam) *
        (deriv (fun lam' => path lam' σ) lam))) = 0

/-- Initial conditions for null geodesic. -/
structure InitialConditions where
  position : Fin 4 → ℝ  -- x^μ(0)
  direction : Fin 4 → ℝ  -- k^μ = dx^μ/dλ|_{λ=0}
  -- Null condition will be enforced by geodesic structure

/-- Existence of null geodesic with given initial conditions. -/
axiom null_geodesic_exists (g : MetricTensor) (ic : InitialConditions) :
  ∃ geo : NullGeodesic g,
    geo.path 0 = ic.position ∧
    (∀ μ, deriv (fun lam => geo.path lam μ) 0 = ic.direction μ)

/-- Affine parameter transformation preserves geodesic. -/
axiom affine_reparametrization (g : MetricTensor) (geo : NullGeodesic g) (a b : ℝ) (ha : a ≠ 0) :
  let lam' := fun lam => a * lam + b
  ∃ geo' : NullGeodesic g, ∀ lam, geo'.path lam = geo.path (lam' lam)

/-- Straight line in Minkowski is null geodesic. -/
axiom minkowski_straight_line_is_geodesic (x₀ k : Fin 4 → ℝ)
  (h_null : Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
              Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
                (inverse_metric minkowski.toMetricTensor) (x₀) (fun i => if i.val = 0 then μ else ν) (fun _ => 0) *
                k μ * k ν)) = 0) :
  let path := fun lam => fun μ => x₀ μ + lam * k μ
  ∃ geo : NullGeodesic minkowski.toMetricTensor,
    (∀ lam, geo.path lam = path lam)

/-- Uniqueness: Geodesic determined by initial conditions. -/
axiom geodesic_unique (g : MetricTensor) (ic : InitialConditions) (geo1 geo2 : NullGeodesic g) :
  (geo1.path 0 = ic.position ∧ geo2.path 0 = ic.position) →
  (∀ μ, deriv (fun lam => geo1.path lam μ) 0 = ic.direction μ) →
  (∀ μ, deriv (fun lam => geo2.path lam μ) 0 = ic.direction μ) →
  (∀ lam μ, geo1.path lam μ = geo2.path lam μ)

end Geodesics
end Relativity
end IndisputableMonolith
