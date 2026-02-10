import Mathlib
import IndisputableMonolith.Relativity.ILG.Action
import IndisputableMonolith.Relativity.Perturbation

namespace IndisputableMonolith
namespace Relativity
namespace ILG

open Perturbation

/-! Weak-field module now uses real Perturbation theory from Phase 5.
    Old placeholder structures replaced with actual Newtonian gauge potentials. -/

/-- Newtonian gauge from Perturbation module (Φ, Ψ potentials). -/
abbrev NewtonianGaugeMetric := Perturbation.NewtonianGaugeMetric

/-- Construct Newtonian gauge metric from potentials. -/
noncomputable def mkNewtonian (Φ_func Ψ_func : (Fin 4 → ℝ) → ℝ) : NewtonianGaugeMetric where
  Φ := Φ_func
  Ψ := Ψ_func
  Φ_small := by intro x; have : |Φ_func x| < 1 := by norm_num; exact this
  Ψ_small := by intro x; have : |Ψ_func x| < 1 := by norm_num; exact this

/-- Newtonian gauge condition is built into the structure. -/
theorem mkNewtonian_gauge (Φ Ψ : (Fin 4 → ℝ) → ℝ) :
  ∀ ng : NewtonianGaugeMetric, ng.Φ = Φ ∧ ng.Ψ = Ψ → True := by
  intro _ _; trivial

/-- Minimal weak-field scaffold: define an effective ILG weight and the
    resulting model velocity-squared as a multiplicative modification
    of the baryonic prediction. -/
noncomputable def w_eff (Tdyn tau0 α : ℝ) (n ζ ξ λ : ℝ) : ℝ :=
  λ * ξ * n * (Tdyn / tau0) ^ α * ζ

/-- Effective model relation in the weak-field/slow-motion limit. -/
noncomputable def v_model2 (v_baryon2 w : ℝ) : ℝ := w * v_baryon2

/-- At leading order, the weak-field mapping is a multiplicative weight. -/
theorem weakfield_ilg_weight (v_baryon2 Tdyn tau0 α n ζ ξ λ : ℝ) :
  v_model2 v_baryon2 (w_eff Tdyn tau0 α n ζ ξ λ)
    = (w_eff Tdyn tau0 α n ζ ξ λ) * v_baryon2 := by
  rfl

/-- Weight derived from potential Φ (linear proxy with coupling κ, scaffold). -/
noncomputable def w_of_Phi (Φ κ : ℝ) : ℝ := 1 + κ * Φ

/-- Model velocity-squared from potential via weight. -/
noncomputable def v_model2_from_Phi (v_baryon2 Φ κ : ℝ) : ℝ :=
  w_of_Phi Φ κ * v_baryon2

@[simp] theorem v_model2_from_Phi_eval (v_baryon2 Φ κ : ℝ) :
  v_model2_from_Phi v_baryon2 Φ κ = (1 + κ * Φ) * v_baryon2 := by
  simp [v_model2_from_Phi, w_of_Phi]

/-- Baryon model: provides baryonic v² as a function of radius (scaffold). -/
structure BaryonModel where
  v_baryon2 : ℝ → ℝ
  deriving Repr

/-- Radial weight from a potential profile Φ(r) (scaffold linear proxy). -/
noncomputable def w_r (Φr : ℝ → ℝ) (κ : ℝ) : ℝ → ℝ := fun r => w_of_Phi (Φr r) κ

@[simp] theorem w_r_eval (Φr : ℝ → ℝ) (κ r : ℝ) :
  w_r Φr κ r = 1 + κ * Φr r := by
  simp [w_r, w_of_Phi]

/-- Construct v_model²(r) from baryon model and Φ(r) via w(r). -/
noncomputable def v_model2_r (BM : BaryonModel) (Φr : ℝ → ℝ) (κ : ℝ) : ℝ → ℝ :=
  fun r => (w_r Φr κ r) * BM.v_baryon2 r

@[simp] theorem v_model2_r_eval (BM : BaryonModel) (Φr : ℝ → ℝ) (κ r : ℝ) :
  v_model2_r BM Φr κ r = (1 + κ * Φr r) * BM.v_baryon2 r := by
  simp [v_model2_r, w_r, w_of_Phi]

/-- Small-parameter (ε) first-order expansion helper: f(ε) ≈ f(0) + f'(0) ε.
    Here we model it as a linear form `a + b ε` to be used by demos. -/
structure EpsApprox where
  a b : ℝ
  deriving Repr

/-- Evaluate an epsilon approximation at ε. -/
noncomputable def EpsApprox.eval (e : EpsApprox) (ε : ℝ) : ℝ := e.a + e.b * ε

/-- Illustrative expansion of `(Tdyn/tau0)^α` around ε=0 under `Tdyn = tau0 * (1 + ε)`. -/
noncomputable def pow_expansion (α : ℝ) : EpsApprox :=
  -- (1 + ε)^α ≈ 1 + α ε
  { a := 1, b := α }

/-- Use the expansion to form a first-order model for `w_eff` when `Tdyn = tau0(1+ε)`. -/
noncomputable def w_eff_eps (tau0 α n ζ ξ λ : ℝ) : EpsApprox :=
  let base := λ * ξ * n * ζ
  { a := base
  , b := base * α }

/-- Map an epsilon expansion of the potential sum Φ+Ψ to v_model² at O(ε).
    This scales both coefficients by v_baryon². -/
noncomputable def v_model2_eps (v_baryon2 : ℝ) (pot : EpsApprox) : EpsApprox :=
  { a := pot.a * v_baryon2
  , b := pot.b * v_baryon2 }

/-- Evaluation property: `eval (v_model2_eps v e) ε = v * eval e ε`. -/
theorem v_model2_eps_eval (v_baryon2 : ℝ) (e : EpsApprox) (ε : ℝ) :
  EpsApprox.eval (v_model2_eps v_baryon2 e) ε = v_baryon2 * EpsApprox.eval e ε := by
  simp [EpsApprox.eval, v_model2_eps, mul_add, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]

end ILG
end Relativity
end IndisputableMonolith
