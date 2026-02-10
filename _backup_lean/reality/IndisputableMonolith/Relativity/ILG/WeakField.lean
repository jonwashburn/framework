import Mathlib
import IndisputableMonolith.Relativity.ILG.Action
import IndisputableMonolith.Relativity.Perturbation
import IndisputableMonolith.ILG.ParamsKernel

open scoped Real

namespace IndisputableMonolith
namespace Relativity
namespace ILG

open Perturbation
open IndisputableMonolith.ILG

/-! Weak-field module now uses real Perturbation theory from Phase 5.
    Old placeholder structures replaced with actual Newtonian gauge potentials. -/

/-- Newtonian gauge from Perturbation module (Φ, Ψ potentials). -/
abbrev NewtonianGaugeMetric := Perturbation.NewtonianGaugeMetric

/-- Construct Newtonian gauge metric from potentials (assuming they are small). -/
noncomputable def mkNewtonian (Φ_func Ψ_func : (Fin 4 → ℝ) → ℝ)
    (hΦ : ∀ x, |Φ_func x| < 0.5) (hΨ : ∀ x, |Ψ_func x| < 0.5) : NewtonianGaugeMetric where
  Φ := Φ_func
  Ψ := Ψ_func
  Φ_small := hΦ
  Ψ_small := hΨ

/-- Newtonian gauge condition is built into the structure. -/
theorem mkNewtonian_gauge (Φ Ψ : (Fin 4 → ℝ) → ℝ)
    (hΦ : ∀ x, |Φ x| < 0.5) (hΨ : ∀ x, |Ψ x| < 0.5) :
  (mkNewtonian Φ Ψ hΦ hΨ).Φ = Φ ∧ (mkNewtonian Φ Ψ hΦ hΨ).Ψ = Ψ := by
  constructor <;> rfl

/-- Minimal weak-field scaffold: define an effective ILG weight and the
    resulting model velocity-squared as a multiplicative modification
    of the baryonic prediction. -/
noncomputable def w_eff (Tdyn tau0 α : ℝ) (n ζ ξ lam : ℝ) : ℝ :=
  lam * ξ * n * (Tdyn / tau0) ^ α * ζ

/-- Effective model relation in the weak-field/slow-motion limit. -/
noncomputable def v_model2 (v_baryon2 w : ℝ) : ℝ := w * v_baryon2

/-- At leading order, the weak-field mapping is a multiplicative weight. -/
theorem weakfield_ilg_weight (v_baryon2 Tdyn tau0 α n ζ ξ lam : ℝ) :
  v_model2 v_baryon2 (w_eff Tdyn tau0 α n ζ ξ lam)
    = (w_eff Tdyn tau0 α n ζ ξ lam) * v_baryon2 := by
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
  a : ℝ
  b : ℝ

/-- Evaluate an epsilon approximation at ε. -/
noncomputable def EpsApprox.eval (e : EpsApprox) (ε : ℝ) : ℝ := e.a + e.b * ε

/-- Illustrative expansion of `(Tdyn/tau0)^α` around ε=0 under `Tdyn = tau0 * (1 + ε)`. -/
noncomputable def pow_expansion (α : ℝ) : EpsApprox :=
  -- (1 + ε)^α ≈ 1 + α ε
  { a := 1, b := α }

/-- Use the expansion to form a first-order model for `w_eff` when `Tdyn = tau0(1+ε)`. -/
noncomputable def w_eff_eps (tau0 α n ζ ξ lam : ℝ) : EpsApprox :=
  let base := lam * ξ * n * ζ
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

/-! ### ILG time-kernel basic facts used by WeakfieldILGCert -/

-- Stub definitions for ILG time kernel (to be fleshed out when full ILG module is available)
noncomputable def εt : ℝ := 0.01

noncomputable def w_t (P : Relativity.ILG.Params) (Tdyn τ0 : ℝ) : ℝ :=
  1 + P.Clag * (max εt (Tdyn / τ0)) ^ P.alpha

lemma epsilon_t_pos : 0 < εt := by
  unfold εt; norm_num

lemma epsilon_t_le_one : εt ≤ 1 := by
  unfold εt; norm_num

lemma time_kernel_le_one_of_le (P : Relativity.ILG.Params) (hP : ParamProps P)
    {Tdyn τ0 : ℝ} (hτ : 0 < τ0) (hT : Tdyn ≤ τ0) (hTdyn_nonneg : 0 ≤ Tdyn)
    (hClag_le : P.Clag ≤ 0) :
    w_t P Tdyn τ0 ≤ 1 := by
  unfold w_t
  -- When Clag ≤ 0, the correction term is ≤ 0
  have hmax_pos : 0 < max εt (Tdyn / τ0) := lt_max_of_lt_left epsilon_t_pos
  have hpow_nonneg : 0 ≤ (max εt (Tdyn / τ0)) ^ P.alpha :=
    Real.rpow_nonneg (le_of_lt hmax_pos) P.alpha
  have hcorr : P.Clag * (max εt (Tdyn / τ0)) ^ P.alpha ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hClag_le hpow_nonneg
  linarith

lemma time_kernel_ge_one_of_ge (P : Relativity.ILG.Params) (hP : ParamProps P)
    {Tdyn τ0 : ℝ} (hτ : 0 < τ0) (hT : τ0 ≤ Tdyn) :
    1 ≤ w_t P Tdyn τ0 := by
  unfold w_t
  -- The correction term is non-negative when Clag ≥ 0
  have hmax_pos : 0 < max εt (Tdyn / τ0) := lt_max_of_lt_left epsilon_t_pos
  have hpow_nonneg : 0 ≤ (max εt (Tdyn / τ0)) ^ P.alpha :=
    Real.rpow_nonneg (le_of_lt hmax_pos) P.alpha
  have hcorr : 0 ≤ P.Clag * (max εt (Tdyn / τ0)) ^ P.alpha :=
    mul_nonneg hP.Clag_nonneg hpow_nonneg
  linarith

lemma time_kernel_eq_one_of_clag_zero (P : Relativity.ILG.Params) (h : P.Clag = 0)
    (Tdyn τ0 : ℝ) : w_t P Tdyn τ0 = 1 := by
  simp [w_t, h]

lemma time_kernel_eq_one_plus_clag_of_alpha_zero (P : Relativity.ILG.Params) (h : P.alpha = 0)
    (Tdyn τ0 : ℝ) : w_t P Tdyn τ0 = 1 + P.Clag := by
  -- When alpha = 0, (max εt (Tdyn/τ0))^0 = 1, so result is 1 + Clag * 1 = 1 + Clag
  simp only [w_t, h, Real.rpow_zero, mul_one]
