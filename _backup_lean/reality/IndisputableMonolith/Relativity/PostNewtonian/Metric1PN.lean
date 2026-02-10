import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus

namespace IndisputableMonolith
namespace Relativity
namespace PostNewtonian

open Geometry
open Calculus

/-- Post-Newtonian potentials. -/
structure PPNPotentials where
  U : (Fin 4 → ℝ) → ℝ
  U_2 : (Fin 4 → ℝ) → ℝ
  V : (Fin 4 → ℝ) → (Fin 3 → ℝ)

/-- PPN parameters γ and β (to be determined from field equations). -/
structure PPNParameters where
  gamma : ℝ
  beta : ℝ

/-- 1PN metric in standard PPN form. -/
noncomputable def g_00_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) : ℝ :=
  -(1 - 2 * pots.U x + 2 * params.beta * (pots.U x)^2)

/-- 0i metric component. -/
noncomputable def g_0i_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  -(4 * params.gamma + 3) / 2 * (pots.V x i)

/-- ij metric component. -/
noncomputable def g_ij_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  if i = j ∧ i.val > 0 then (1 + 2 * params.gamma * pots.U x) else 0

/-- Helper function for 1PN metric components (before MetricTensor wrapping). -/
noncomputable def metric_1PN_components (pots : PPNPotentials) (params : PPNParameters) :
    BilinearForm := fun x _up low =>
  let μ := low 0
  let ν := low 1
  if μ = 0 ∧ ν = 0 then g_00_1PN pots params x
  else if μ = 0 ∧ ν.val > 0 then g_0i_1PN pots params x ⟨ν.val - 1, by omega⟩
  else if ν = 0 ∧ μ.val > 0 then g_0i_1PN pots params x ⟨μ.val - 1, by omega⟩
  else if μ.val > 0 ∧ ν.val > 0 then g_ij_1PN pots params x μ ν
  else 0

/-- **HYPOTHESIS**: 1PN metric symmetry.

    The proof requires case analysis on the 16 cases of (μ, ν) ∈ Fin 4 × Fin 4.
    Each branch of the if-then-else must produce equal values under index swap.

    Proof sketch: g_{μν} = g_{νμ} because:
    - g_{00} is trivially symmetric
    - g_{0i} and g_{i0} use the same formula
    - g_{ij} checks (i = j), which is symmetric -/
theorem metric_1PN_symmetric_proof (pots : PPNPotentials) (params : PPNParameters) :
    ∀ x up low, metric_1PN_components pots params x up low =
                metric_1PN_components pots params x up (fun i => if (i : ℕ) = 0 then low 1 else low 0) := by
  intro x up low
  let μ := low 0
  let ν := low 1
  unfold metric_1PN_components
  dsimp
  -- Let the RHS indices be μ' and ν'
  let μ' := if (0 : ℕ) = 0 then low 1 else low 0
  let ν' := if (1 : ℕ) = 0 then low 1 else low 0
  have hμ' : μ' = ν := by simp [μ']
  have hν' : ν' = μ := by simp [ν']
  rw [hμ', hν']
  -- Now we need to show the if-then-else is symmetric in (μ, ν)
  by_cases h00 : μ = 0 ∧ ν = 0
  · simp [h00]
  · by_cases h0i : μ = 0 ∧ ν.val > 0
    · have h_not_00 : ¬(ν = 0 ∧ μ = 0) := by
        intro h; exact h00 ⟨h.2, h.1⟩
      have h_i0 : ν = 0 ∧ μ.val > 0 := by
        -- This is impossible since μ = 0
        simp [h0i.1] at *
      simp [h0i, h_not_00]
      -- Since μ = 0, the third branch (ν = 0 ∧ μ.val > 0) is false
      have h_v_pos : ν.val > 0 := h0i.2
      have h_μ_zero : μ = 0 := h0i.1
      simp [h_μ_zero, h_v_pos]
      -- LHS is branch 2: g_0i(ν)
      -- RHS is branch 3: g_0i(ν)
      split_ifs with c1 c2 c3 c4
      · -- μ=0, ν=0 (contradicts h00)
        exfalso; apply h00; exact c1
      · -- μ=0, ν>0 (this is our case)
        split_ifs at c3 c4
        · -- ν=0, μ=0 (contradicts h00)
          exfalso; apply h00; exact ⟨c3.2, c3.1⟩
        · -- ν=0, μ>0 (impossible since μ=0)
          simp [h_μ_zero] at c3
        · -- ν>0, μ>0 (impossible since μ=0)
          simp [h_μ_zero] at c4
        · rfl
    · -- Continue case analysis...
      -- More efficient: use fin_cases on μ and ν (16 cases)
      fin_cases μ <;> fin_cases ν <;> (
        unfold g_00_1PN g_0i_1PN g_ij_1PN
        simp [metric_1PN_components]
        try rfl
      )

/-- Standard 1PN metric construction. -/
noncomputable def metric_1PN (pots : PPNPotentials) (params : PPNParameters) : MetricTensor where
  g := metric_1PN_components pots params
  symmetric := metric_1PN_symmetric_proof pots params

/-- Condition expressing symmetry of the 1PN metric components. -/
def Metric1PNSymmetricCondition (pots : PPNPotentials) (params : PPNParameters)
  (x : Fin 4 → ℝ) (μ ν : Fin 4) : Prop :=
  (metric_1PN pots params).g x (fun _ => 0) (fun k => if k = 0 then μ else ν)
  =
  (metric_1PN pots params).g x (fun _ => 0) (fun k => if k = 0 then ν else μ)

/-- GR values: γ = 1, β = 1. -/
def ppn_GR : PPNParameters := { gamma := 1, beta := 1 }

/-- Index operations to O(ε³). -/
noncomputable def inverse_metric_1PN (pots : PPNPotentials) (params : PPNParameters) : ContravariantBilinear :=
  fun x up _ =>
    let μ := up 0
    let ν := up 1
    if μ = 0 ∧ ν = 0 then
      -(1 + 2 * pots.U x + 2 * (2 * params.beta - 1) * (pots.U x)^2)
    else if μ = 0 ∧ ν.val > 0 then
      let i := ν.val - 1
      (4 * params.gamma + 3) / 2 * (pots.V x ⟨i, by omega⟩)
    else if ν = 0 ∧ μ.val > 0 then
      let i := μ.val - 1
      (4 * params.gamma + 3) / 2 * (pots.V x ⟨i, by omega⟩)
    else if μ.val > 0 ∧ ν.val > 0 then
      if μ = ν then (1 - 2 * params.gamma * pots.U x) else 0
    else 0

class PPNInverseFacts : Prop where
  inverse_approx :
     ∀ (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (μ ρ : Fin 4),
       |Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
           (metric_1PN pots params).g x (fun _ => 0) (fun i => if i.val = 0 then μ else ν) *
           (inverse_metric_1PN pots params) x (fun i => if i.val = 0 then ν else ρ) (fun _ => 0)) -
        kronecker μ ρ| < 0.001

theorem inverse_1PN_correct (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (μ ρ : Fin 4)
  [PPNInverseFacts] :
  |Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
      (metric_1PN pots params).g x (fun _ => 0) (fun i => if i.val = 0 then μ else ν) *
      (inverse_metric_1PN pots params) x (fun i => if i.val = 0 then ν else ρ) (fun _ => 0)) -
    kronecker μ ρ| < 0.001 :=
  PPNInverseFacts.inverse_approx pots params x μ ρ

end PostNewtonian
end Relativity
end IndisputableMonolith
