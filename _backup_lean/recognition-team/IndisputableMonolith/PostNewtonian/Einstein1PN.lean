import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Variation
import IndisputableMonolith.Relativity.PostNewtonian.Metric1PN

namespace IndisputableMonolith
namespace Relativity
namespace PostNewtonian

open Geometry
open Calculus
open Fields
open Variation

/-- Einstein tensor 00-component to O(ε³). -/
noncomputable def G_00_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) : ℝ :=
  laplacian pots.U x +
  laplacian pots.U_2 x -
  2 * Finset.sum (Finset.univ : Finset (Fin 3)) (fun i => (partialDeriv_v2 pots.U (i.succ) x)^2) -
  4 * pots.U x * laplacian pots.U x

/-- Einstein tensor 0i-component to O(ε^{5/2}). -/
noncomputable def G_0i_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  let i' : Fin 4 := ⟨i.val + 1, by omega⟩
  laplacian (fun y => pots.V y i) x -
  partialDeriv_v2 (fun y => partialDeriv_v2 pots.U 0 y) i' x

/-- Einstein tensor ij-component to O(ε²). -/
noncomputable def G_ij_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  if i = j ∧ i.val > 0 then
    params.gamma * laplacian pots.U x
  else 0

/-- Stress-energy 00-component to O(ε³) including scalar field. -/
noncomputable def T_00_1PN (ψ : Fields.ScalarField) (pots : PPNPotentials) (α m_squared : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  let grad_ψ := gradient ψ x
  let ψ_val := ψ.ψ x
  (α / 2) * Finset.sum (Finset.range 3) (fun i =>
    let i_plus_1 := i + 1
    if h : i_plus_1 < 4 then
      let i' : Fin 4 := ⟨i_plus_1, h⟩
      (grad_ψ i')^2
    else 0) +
  (m_squared / 2) * ψ_val^2

/-- Stress-energy 0i-component to O(ε^{5/2}). -/
noncomputable def T_0i_1PN (ψ : Fields.ScalarField) (α : ℝ) (x : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  let i' : Fin 4 := ⟨i.val + 1, by omega⟩
  α * partialDeriv_v2 ψ.ψ 0 x * partialDeriv_v2 ψ.ψ i' x

/-- Stress-energy ij-component to O(ε²). -/
noncomputable def T_ij_1PN (ψ : Fields.ScalarField) (α m_squared : ℝ) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  if i = j ∧ i.val > 0 ∧ j.val > 0 then
    let grad_ψ := gradient ψ x
    let ψ_val := ψ.ψ x
    α * (grad_ψ i) * (grad_ψ j) -
    (1/2) * (Finset.sum (Finset.range 3) (fun k =>
      let k_plus_1 := k + 1
      if h : k_plus_1 < 4 then
        let k' : Fin 4 := ⟨k_plus_1, h⟩
        (grad_ψ k')^2
      else 0) - m_squared * ψ_val^2)
  else 0

/-- 1PN Einstein equation (00-component): G_00 = κ T_00. -/
def Einstein00_1PN (pots : PPNPotentials) (params : PPNParameters) (ψ : Fields.ScalarField)
  (ρ_matter : (Fin 4 → ℝ) → ℝ) (α m_squared : ℝ) : Prop :=
  ∀ x, let κ := (1 : ℝ)
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
  constructor
  · intro x
    have h00 := h.eq_00 x
    simp only [T_00_1PN, zero_ψ, mul_zero, add_zero, zero_mul] at h00
    -- Wait, Fields.zero is defined as constant 0.
    -- Let's check how T_00_1PN handles Fields.zero.
    unfold T_00_1PN at h00
    simp only [mul_zero, add_zero, zero_mul] at h00
    exact h00
  · constructor
    · intro x i
      have h0i := h.eq_0i x i
      simp only [T_0i_1PN, zero_mul, mul_zero] at h0i
      exact h0i
    · intro x i j
      have hij := h.eq_ij x i j
      simp only [T_ij_1PN, mul_zero, zero_mul, sub_zero, if_true] at hij
      -- If i = j ∧ i.val > 0 ∧ j.val > 0 then ...
      split_ifs at hij with h_cond
      · simp only [mul_zero, zero_mul, sub_zero] at hij
        exact hij
      · exact hij

end PostNewtonian
end Relativity
end IndisputableMonolith
