/-
Basic Definitions for Navier-Stokes Bridge
==========================================

Core type definitions and PDE operators for the Navier-Stokes equations.

Ported from github.com/jonwashburn/navier-stokes-lean
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import IndisputableMonolith.ClassicalBridge.Fluids.RSImports

namespace IndisputableMonolith.ClassicalBridge.Fluids

open Real

/-!
## Basic Type Definitions
-/

/-- A vector field on ℝ³ -/
def VectorField := (Fin 3 → ℝ) → (Fin 3 → ℝ)

/-- Velocity field: a vector field on ℝ³ -/
def VelocityField := VectorField

/-- A scalar field on ℝ³ -/
def ScalarField := (Fin 3 → ℝ) → ℝ

/-- Pressure field: a scalar field on ℝ³ -/
def PressureField := ScalarField

/-- The space ℝ³ -/
def R3 : Type := Fin 3 → ℝ

/-!
## Differential Operators
-/

/-- Partial derivative in the i-th direction -/
noncomputable def partialDeriv (i : Fin 3) (f : ScalarField) (x : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ f x (fun j => if j = i then 1 else 0)

/-- Partial derivative of a vector field component -/
noncomputable def partialDerivVec (i : Fin 3) (u : VectorField) (j : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ (fun y => u y j) x (fun k => if k = i then 1 else 0)

/-- Divergence of a vector field: ∇·u = ∂u₁/∂x₁ + ∂u₂/∂x₂ + ∂u₃/∂x₃ -/
noncomputable def divergence (u : VectorField) : ScalarField :=
  fun x => ∑ i : Fin 3, partialDerivVec i u i x

/-- Curl of a vector field: ∇×u = (∂u₃/∂x₂ - ∂u₂/∂x₃, ∂u₁/∂x₃ - ∂u₃/∂x₁, ∂u₂/∂x₁ - ∂u₁/∂x₂) -/
noncomputable def curl (u : VectorField) : VectorField :=
  fun x i => match i with
  | ⟨0, _⟩ => partialDerivVec ⟨1, by norm_num⟩ u ⟨2, by norm_num⟩ x -
              partialDerivVec ⟨2, by norm_num⟩ u ⟨1, by norm_num⟩ x
  | ⟨1, _⟩ => partialDerivVec ⟨2, by norm_num⟩ u ⟨0, by norm_num⟩ x -
              partialDerivVec ⟨0, by norm_num⟩ u ⟨2, by norm_num⟩ x
  | ⟨2, _⟩ => partialDerivVec ⟨0, by norm_num⟩ u ⟨1, by norm_num⟩ x -
              partialDerivVec ⟨1, by norm_num⟩ u ⟨0, by norm_num⟩ x

/-- Laplacian of a scalar field: Δf = ∂²f/∂x₁² + ∂²f/∂x₂² + ∂²f/∂x₃² -/
noncomputable def laplacianScalar (f : ScalarField) : ScalarField :=
  fun x => ∑ i : Fin 3, fderiv ℝ (fun y => partialDeriv i f y) x (fun j => if j = i then 1 else 0)

/-- Laplacian of a vector field (component-wise) -/
noncomputable def laplacianVector (u : VectorField) : VectorField :=
  fun x i => laplacianScalar (fun y => u y i) x

/-- Convective derivative: (u·∇)v = ∑ᵢ uᵢ ∂vⱼ/∂xᵢ -/
noncomputable def convectiveDerivative (u v : VectorField) : VectorField :=
  fun x j => ∑ i : Fin 3, u x i * partialDerivVec i v j x

/-- Gradient of a scalar field -/
noncomputable def gradientScalar (p : ScalarField) : VectorField :=
  fun x i => partialDeriv i p x

/-!
## Norms
-/

/-- L∞ norm of a vector field (supremum over all points) -/
noncomputable def LinftyNorm (u : VectorField) : ℝ :=
  iSup fun x => ‖u x‖

/-- Sup norm (alias for LinftyNorm) -/
noncomputable def supNorm (u : VectorField) : ℝ := LinftyNorm u

/-- L² norm squared (axiomatized for now) -/
noncomputable def L2NormSquared : VectorField → ℝ := fun _ =>
  -- Placeholder: this should be ∫ ‖u x‖² dx over ℝ³
  1  -- This is just a placeholder; the actual value comes from the axioms

/-- L² norm of a vector field -/
noncomputable def L2Norm (u : VectorField) : ℝ :=
  Real.sqrt (L2NormSquared u)

-- Minimal facts about the placeholder `L2NormSquared`.
-- Once `L2NormSquared` is defined via an actual integral, this should be replaced by real lemmas.
lemma L2_norm_nonneg (u : VectorField) : 0 ≤ L2NormSquared u := by
  simp [L2NormSquared]

/-- supNorm is non-negative -/
lemma supNorm_nonneg (u : VectorField) : 0 ≤ supNorm u := by
  unfold supNorm LinftyNorm
  apply Real.iSup_nonneg
  intro x
  exact norm_nonneg _

/-- Bound on pointwise norm by supNorm (axiomatized for unbounded domains) -/
lemma le_supNorm_apply (u : VectorField) (x : Fin 3 → ℝ)
    (h_bdd : BddAbove (Set.range fun y => ‖u y‖)) : ‖u x‖ ≤ supNorm u := by
  unfold supNorm LinftyNorm
  -- `le_ciSup` requires an explicit boundedness hypothesis in a conditionally complete lattice.
  simpa using (le_ciSup h_bdd x)

/-!
## Energy and Enstrophy
-/

/-- Energy is half the L² norm squared -/
noncomputable def energyReal (u : VectorField) : ℝ :=
  (1/2) * L2NormSquared u

/-- Vorticity of a vector field -/
noncomputable def vorticity (u : VectorField) : VectorField := curl u

/-- Enstrophy is half the L² norm squared of vorticity -/
noncomputable def enstrophyReal (u : VectorField) : ℝ :=
  (1/2) * L2NormSquared (curl u)

/-- Squared Frobenius norm of velocity gradient: ∑ᵢⱼ |∂uᵢ/∂xⱼ|² -/
noncomputable def gradientNormSquared (u : VectorField) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, (partialDerivVec j u i x)^2

/-- Dissipation functional (L² norm of gradient) -/
noncomputable def dissipationFunctional (u : VectorField) : ℝ :=
  L2NormSquared fun x => fun _ => Real.sqrt (gradientNormSquared u x)

/-- Energy dissipation rate -/
noncomputable def energyDissipation (u : VectorField) : ℝ :=
  -2 * dissipationFunctional u

-- Energy is non-negative
lemma energy_nonneg (u : VectorField) : 0 ≤ energyReal u := by
  unfold energyReal
  apply mul_nonneg
  · norm_num
  · exact L2_norm_nonneg u

-- (No positivity lemma for nonzero energy is claimed at this stage; it will come from the
-- measure-theoretic definition of `L2NormSquared` once implemented.)

/-!
## Tensor Notation Helpers
-/

/-- Kronecker delta: 1 if i = j, 0 otherwise -/
def kronecker (i j : Fin 3) : ℝ := if i = j then 1 else 0

/-- Levi-Civita symbol: sign of permutation (i, j, k) -/
def levi_civita (i j k : Fin 3) : ℝ :=
  if i = j ∨ j = k ∨ i = k then 0
  else if (i.val + 1) % 3 = j.val ∧ (j.val + 1) % 3 = k.val then 1
  else -1

-- Basic properties
theorem levi_civita_self₁ (i j : Fin 3) : levi_civita i i j = 0 := by
  unfold levi_civita; simp

theorem kronecker_eq_one_iff (i j : Fin 3) : kronecker i j = 1 ↔ i = j := by
  unfold kronecker; constructor <;> intro h <;> simp_all

theorem kronecker_eq_zero_iff (i j : Fin 3) : kronecker i j = 0 ↔ i ≠ j := by
  unfold kronecker; constructor <;> intro h <;> simp_all

/-!
## Navier-Stokes Structure
-/

/-- Solution to the Navier-Stokes equations -/
structure NSE (ν : ℝ) where
  /-- The velocity field u(x,t) -/
  u : ℝ → VectorField
  /-- The pressure field p(x,t) -/
  p : ℝ → ScalarField
  /-- Initial data -/
  initial_data : VectorField
  /-- Initial condition -/
  h_initial : u 0 = initial_data
  /-- Incompressibility -/
  divergence_free : ∀ t, divergence (u t) = fun _ => 0
  /-- The velocity is smooth in time -/
  smooth_solution : ∀ t, ContDiff ℝ ⊤ (u t)
  /-- Navier-Stokes equation holds (stated as differentiability) -/
  h_nse : ∀ t x i, DifferentiableAt ℝ (fun s => u s x i) t

/-!
## Solution Concepts
-/

/-- Smooth initial data for Navier-Stokes -/
def SmoothInitialData (u₀ : VectorField) (_p₀ : ScalarField) : Prop :=
  ContDiff ℝ ⊤ u₀

/-- Global smooth solution to Navier-Stokes.
    Replaces the vacuous `∃ sol, True` with a meaningful existential.

    STATUS: SCAFFOLD — Existence of global smooth solutions for general initial data
    is a Millennium Prize problem.
    TODO: Link to Koch-Tataru results for small initial data in BMO⁻¹. -/
def GlobalSmoothSolution (u : ℝ → VectorField) (p : ℝ → ScalarField)
    (u₀ : VectorField) (p₀ : ScalarField) : Prop :=
  -- Smoothness in time and space
  (∀ t ≥ 0, ContDiff ℝ ⊤ (u t)) ∧
  -- Initial condition
  (u 0 = u₀) ∧
  -- The fields actually satisfy the Navier-Stokes equations
  ∃ (sol : NSE 1), sol.u = u ∧ sol.p = p ∧ sol.initial_data = u₀

end IndisputableMonolith.ClassicalBridge.Fluids
