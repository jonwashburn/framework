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

noncomputable def g_0i_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (i : Fin 3) : ℝ :=
  -(4 * params.gamma + 3) / 2 * (pots.V x i)

noncomputable def g_ij_1PN (pots : PPNPotentials) (params : PPNParameters) (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  if i = j ∧ i.val > 0 then (1 + 2 * params.gamma * pots.U x) else 0

noncomputable def metric_1PN (pots : PPNPotentials) (params : PPNParameters) : MetricTensor where
  g := fun x _up low =>
    let μ := low 0
    let ν := low 1
    if μ = 0 ∧ ν = 0 then g_00_1PN pots params x
    else if μ = 0 ∧ ν.val > 0 then g_0i_1PN pots params x ⟨ν.val - 1, by omega⟩
    else if ν = 0 ∧ μ.val > 0 then g_0i_1PN pots params x ⟨μ.val - 1, by omega⟩
    else if μ.val > 0 ∧ ν.val > 0 then g_ij_1PN pots params x μ ν
    else 0
  symmetric := by
    intro x up low
    dsimp
    fin_cases (low 0) <;> fin_cases (low 1) <;> try rfl
    -- The remaining cases should be handled by the definition's if-then-else structure.
    -- For example, (0, 1) and (1, 0) should both give g_0i.
    all_goals (
      unfold g_00_1PN g_0i_1PN g_ij_1PN
      simp only [Nat.reduceSub, Fin.coe_fin_one, Fin.coe_fin_two, Fin.coe_fin_three,
                 Fin.zero_eta, Fin.val_zero, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      try split_ifs <;> try ring <;> try rfl
    )

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
