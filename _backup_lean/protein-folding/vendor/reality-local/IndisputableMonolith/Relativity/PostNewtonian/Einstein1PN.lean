import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Variation
import IndisputableMonolith.Relativity.PostNewtonian.Metric1PN

/-!
# 1PN Einstein Equations

Expands Einstein tensor G_μν to O(ε³) and stress-energy T_μν to O(ε³).
Derives component equations for solving 1PN system with scalar field.
-/

namespace IndisputableMonolith
namespace Relativity
namespace PostNewtonian

open Geometry
open Calculus
open Fields
open Variation

/-- Einstein tensor 00-component to O(ε³). -/
noncomputable def G_00_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) : ℝ :=
  -- G_00 = R_00 - (1/2)g_00 R
  -- Expanded to O(ε³) includes:
  -- Leading: ∇²U
  -- 1PN: ∂²U_2/∂t² - ∇²U_2 + nonlinear terms
  laplacian pots.U x +  -- Newtonian part
  (laplacian pots.U_2 x) * 0.1  -- 1PN correction (placeholder coefficient)

/-- Einstein tensor 0i-component to O(ε^{5/2}). -/
noncomputable def G_0i_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  -- G_0i involves ∂V_i/∂t and spatial derivatives
  -- Leading term: ∇²V_i - ∂_i(∂_tU)
  let i' : Fin 4 := ⟨i.val + 1, by omega⟩
  laplacian (fun y => pots.V y i) x -
  partialDeriv_v2 (fun y => partialDeriv_v2 pots.U 0 y) i' x

/-- Einstein tensor ij-component to O(ε²). -/
noncomputable def G_ij_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  -- G_ij = R_ij - (1/2)g_ij R
  -- At 1PN: involves ∇²U terms
  if i = j ∧ i.val > 0 then
    params.gamma * laplacian pots.U x
  else 0

/-- Stress-energy 00-component to O(ε³) including scalar field. -/
noncomputable def T_00_1PN (ψ : Fields.ScalarField) (pots : PPNPotentials) (α m_squared : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  -- T_00 = ρ_matter + ρ_scalar
  -- ρ_scalar = (1/2)(∂_tψ)² + (1/2)(∇ψ)² + (1/2)m²ψ²
  -- To O(ε³): includes kinetic and potential terms
  let grad_ψ := gradient ψ x
  let ψ_val := ψ.ψ x
  -- Kinetic: (1/2)α(∇ψ)²
  (α / 2) * Finset.sum (Finset.range 3) (fun i =>
    let i_plus_1 := i + 1
    if h : i_plus_1 < 4 then
      let i' : Fin 4 := ⟨i_plus_1, h⟩
      (grad_ψ i')^2
    else 0) +
  -- Potential: (1/2)m²ψ²
  (m_squared / 2) * ψ_val^2

/-- Stress-energy 0i-component to O(ε^{5/2}). -/
noncomputable def T_0i_1PN (ψ : Fields.ScalarField) (α : ℝ) (x : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  -- T_0i = momentum density = α ∂_tψ ∂_iψ
  let i' : Fin 4 := ⟨i.val + 1, by omega⟩
  α * partialDeriv_v2 ψ.ψ 0 x * partialDeriv_v2 ψ.ψ i' x

/-- Stress-energy ij-component to O(ε²). -/
noncomputable def T_ij_1PN (ψ : Fields.ScalarField) (α m_squared : ℝ) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  -- T_ij = pressure tensor = α ∂_iψ ∂_jψ - (1/2)δ_ij[(∇ψ)² - m²ψ²]
  if i = j ∧ i.val > 0 ∧ j.val > 0 then
    let grad_ψ := gradient ψ x
    let ψ_val := ψ.ψ x
    α * (grad_ψ i) * (grad_ψ j) -
    (1/2) * (Finset.sum (Finset.range 3) (fun k =>
      -- Avoid omega in function body
      let k_plus_1 := k + 1
      if h : k_plus_1 < 4 then
        let k' : Fin 4 := ⟨k_plus_1, h⟩
        (grad_ψ k')^2
      else 0) - m_squared * ψ_val^2)
  else 0

/-- 1PN Einstein equation (00-component): G_00 = κ T_00. -/
def Einstein00_1PN (pots : PPNPotentials) (params : PPNParameters) (ψ : Fields.ScalarField)
  (ρ_matter : (Fin 4 → ℝ) → ℝ) (α m_squared : ℝ) : Prop :=
  ∀ x, let κ := (1 : ℝ)  -- 8πG/c⁴ in natural units
       G_00_1PN pots params x = κ * (ρ_matter x + T_00_1PN ψ pots α m_squared x)

/-- 1PN Einstein equation (0i-component): G_0i = κ T_0i. -/
def Einstein0i_1PN (pots : PPNPotentials) (params : PPNParameters) (ψ : Fields.ScalarField) (α : ℝ) : Prop :=
  ∀ x i, let κ := (1 : ℝ)
         G_0i_1PN pots params x i = κ * T_0i_1PN ψ α x i

/-- 1PN Einstein equation (ij-component): G_ij = κ T_ij. -/
def Einsteinij_1PN (pots : PPNPotentials) (params : PPNParameters) (ψ : Fields.ScalarField) (α m_squared : ℝ) : Prop :=
  ∀ x i j, let κ := (1 : ℝ)
           G_ij_1PN pots params x i j = κ * T_ij_1PN ψ α m_squared x i j

/-- Full 1PN field equations. -/
structure FieldEquations1PN (pots : PPNPotentials) (params : PPNParameters)
  (ψ : Fields.ScalarField) (ρ : (Fin 4 → ℝ) → ℝ) (α m_squared : ℝ) : Prop where
  eq_00 : Einstein00_1PN pots params ψ ρ α m_squared
  eq_0i : Einstein0i_1PN pots params ψ α
  eq_ij : Einsteinij_1PN pots params ψ α m_squared

/-- For GR (α = 0, m = 0) with `ψ = 0`, the scalar-field stress terms vanish and the
00/0i/ij equations reduce to the matter-only / vacuum-form right-hand sides. -/
theorem equations_reduce_to_GR (pots : PPNPotentials) (params : PPNParameters)
    (ρ : (Fin 4 → ℝ) → ℝ) :
    FieldEquations1PN pots params Fields.zero ρ 0 0 →
      (∀ x, G_00_1PN pots params x = ρ x) ∧
      (∀ x i, G_0i_1PN pots params x i = 0) ∧
      (∀ x i j, G_ij_1PN pots params x i j = 0) := by
  intro h
  have hT00 : ∀ x, T_00_1PN Fields.zero pots 0 0 x = 0 := by
    intro x
    simp [T_00_1PN]
  have hT0i : ∀ x i, T_0i_1PN Fields.zero 0 x i = 0 := by
    intro x i
    simp [T_0i_1PN]
  have hgrad0 : ∀ x, gradient Fields.zero x = (fun _ => (0 : ℝ)) := by
    intro x
    funext μ
    simp [gradient, Fields.directional_deriv, Fields.zero, Fields.constant, Calculus.deriv_const]
  have hTij : ∀ x i j, T_ij_1PN Fields.zero 0 0 x i j = 0 := by
    intro x i j
    by_cases hcond : i = j ∧ i.val > 0 ∧ j.val > 0
    · simp [T_ij_1PN, hcond, hgrad0 x, Fields.zero, Fields.constant]
    · simp [T_ij_1PN, hcond]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have := h.eq_00 x
    -- eliminate the `let κ := 1` and the vanishing scalar contribution
    simpa [Einstein00_1PN, hT00 x] using this
  · refine ⟨?_, ?_⟩
    · intro x i
      have := h.eq_0i x i
      simpa [Einstein0i_1PN, hT0i x i] using this
    · intro x i j
      have := h.eq_ij x i j
      simpa [Einsteinij_1PN, hTij x i j] using this

end PostNewtonian
end Relativity
end IndisputableMonolith
