import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.Constants
import IndisputableMonolith.Verification.Verification
import IndisputableMonolith.Verification.Dimensionless

/-!
Observable Structure and K-Gate Framework

This module contains the Observable structure for dimensionless displays,
bridge evaluation functions, and K-gate verification framework.
-/

namespace IndisputableMonolith

open Constants
open Verification

/-- Observable: a dimensionless display ready for bridge evaluation. -/
structure Observable where
  f       : RSUnits → ℝ
  dimless : Dimensionless f

/-- Bridge evaluation (A ∘ Q): evaluate any observable under anchors; invariant by construction. -/
@[simp] def BridgeEval (O : Observable) (U : RSUnits) : ℝ := O.f U

/-- Anchor-invariance (Q): evaluation does not depend on rescaled anchors. -/
theorem anchor_invariance (O : Observable) {U U'}
  (hUU' : UnitsRescaled U U') : BridgeEval O U = BridgeEval O U' :=
  O.dimless hUU'

/-- K_A observable equals constant K; dimensionless by definition. -/
noncomputable def K_A_obs : Observable :=
{ f := fun _ => K
, dimless := dimensionless_const K }

/-- K_B observable equals constant K; dimensionless by definition. -/
noncomputable def K_B_obs : Observable :=
{ f := fun _ => K
, dimless := dimensionless_const K }

/-- K-gate bridge: both observables equal the same constant K. -/
theorem K_gate_bridge (U : RSUnits) : BridgeEval K_A_obs U = BridgeEval K_B_obs U := by
  simp [BridgeEval, K_A_obs, K_B_obs]

/-- Uncertainty combiner with correlation: u_comb = √(u_ℓ0^2 + u_λrec^2 − 2ρ u_ℓ0 u_λrec). -/
noncomputable def uComb (u_ell0 u_lrec rho : ℝ) : ℝ :=
  Real.sqrt (u_ell0 ^ 2 + u_lrec ^ 2 - 2 * rho * u_ell0 * u_lrec)

/-- The expression under the square root in `uComb` is nonnegative for |ρ|≤1. -/
lemma uComb_inner_nonneg (u_ell0 u_lrec rho : ℝ)
  (hrho : -1 ≤ rho ∧ rho ≤ 1) :
  0 ≤ u_ell0 ^ 2 + u_lrec ^ 2 - 2 * rho * u_ell0 * u_lrec := by
  -- Rewrite as a sum of squares: (u_ell0 - ρ u_lrec)^2 + (1-ρ^2) u_lrec^2
  have h : u_ell0 ^ 2 + u_lrec ^ 2 - 2 * rho * u_ell0 * u_lrec
           = (u_ell0 - rho * u_lrec) ^ 2 + (1 - rho ^ 2) * (u_lrec ^ 2) := by
    ring
  have h1 : 0 ≤ (u_ell0 - rho * u_lrec) ^ 2 := by exact sq_nonneg _
  have h2 : 0 ≤ (1 - rho ^ 2) := by
    have : rho ^ 2 ≤ 1 ^ 2 := by
      have habs : |rho| ≤ 1 := by
        have hleft : -1 ≤ rho := hrho.left
        have hright : rho ≤ 1 := hrho.right
        exact abs_le.mpr ⟨by simpa [neg_one_le] using hleft, hright⟩
      simpa using (pow_two_le_pow_two_of_le_abs h:=habs)
    have : 0 ≤ 1 - rho ^ 2 := sub_nonneg.mpr this
    simpa using this
  have h3 : 0 ≤ (1 - rho ^ 2) * (u_lrec ^ 2) := mul_nonneg h2 (sq_nonneg _)
  simpa [h] using add_nonneg h1 h3

/-- Route A single‑inequality K‑gate: |K_A − K_B| ≤ k·u_comb for any nonnegative k and |ρ|≤1. -/
theorem K_gate_single_inequality (U : RSUnits)
  (u_ell0 u_lrec rho k : ℝ)
  (hk : 0 ≤ k) (hrho : -1 ≤ rho ∧ rho ≤ 1) :
  Real.abs (BridgeEval K_A_obs U - BridgeEval K_B_obs U)
    ≤ k * uComb u_ell0 u_lrec rho := by
  -- Left side is zero by the bridge identity
  have hEq : BridgeEval K_A_obs U - BridgeEval K_B_obs U = 0 := by
    simpa [sub_eq, K_gate_bridge U]
  -- Right side is nonnegative
  have hroot : 0 ≤ uComb u_ell0 u_lrec rho := by
    dsimp [uComb]
    exact Real.sqrt_nonneg _
  have hinner : 0 ≤ u_ell0 ^ 2 + u_lrec ^ 2 - 2 * rho * u_ell0 * u_lrec :=
    uComb_inner_nonneg u_ell0 u_lrec rho hrho
  have hroot' : 0 ≤ Real.sqrt (u_ell0 ^ 2 + u_lrec ^ 2 - 2 * rho * u_ell0 * u_lrec) :=
    Real.sqrt_nonneg _
  have hrhs : 0 ≤ k * uComb u_ell0 u_lrec rho :=
    mul_nonneg hk hroot'
  -- Conclude
  simpa [hEq, Real.abs_zero] using hrhs

/-- Edge-case check: `K_gate_single_inequality` holds at ρ = 1 with k = 0. -/
@[simp] theorem K_gate_single_inequality_rho_pos1_k0 (U : RSUnits) (u_ell0 u_lrec : ℝ) :
  Real.abs (BridgeEval K_A_obs U - BridgeEval K_B_obs U)
    ≤ 0 * uComb u_ell0 u_lrec (1 : ℝ) := by
  have hk : 0 ≤ (0 : ℝ) := by simp
  have hrho : -1 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1 := by constructor <;> norm_num
  simpa using K_gate_single_inequality U u_ell0 u_lrec (1 : ℝ) 0 hk hrho

/-- Edge-case check: `K_gate_single_inequality` holds at ρ = -1 with k = 0. -/
@[simp] theorem K_gate_single_inequality_rho_neg1_k0 (U : RSUnits) (u_ell0 u_lrec : ℝ) :
  Real.abs (BridgeEval K_A_obs U - BridgeEval K_B_obs U)
    ≤ 0 * uComb u_ell0 u_lrec (-1 : ℝ) := by
  have hk : 0 ≤ (0 : ℝ) := by simp
  have hrho : -1 ≤ (-1 : ℝ) ∧ (-1 : ℝ) ≤ 1 := by constructor <;> norm_num
  simpa using K_gate_single_inequality U u_ell0 u_lrec (-1 : ℝ) 0 hk hrho

/-- Anchor rescaling invariance for constants: `K_A_obs` is invariant under `UnitsRescaled`. -/
@[simp] theorem K_A_obs_anchor_invariant {U U' : RSUnits} (hUU' : UnitsRescaled U U') :
  BridgeEval K_A_obs U = BridgeEval K_A_obs U' := by
  simpa using anchor_invariance K_A_obs hUU'

/-- Anchor rescaling invariance for constants: `K_B_obs` is invariant under `UnitsRescaled`. -/
@[simp] theorem K_B_obs_anchor_invariant {U U' : RSUnits} (hUU' : UnitsRescaled U U') :
  BridgeEval K_B_obs U = BridgeEval K_B_obs U' := by
  simpa using anchor_invariance K_B_obs hUU'

end IndisputableMonolith