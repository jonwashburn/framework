import IndisputableMonolith.Fusion.PowerBalance
import IndisputableMonolith.Fusion.ReactivityProxy

/-!
# Power-Balance Inequality Bounds (Lean-Proved)

This module pushes the power-balance story one step further:

1. We **commit** to a concrete reactivity proxy `⟨σv⟩_proxy(T) = T·exp(-η(T))`
   (module `Fusion.ReactivityProxy`).
2. We reuse the concrete bremsstrahlung + transport loss model from `Fusion.PowerBalance`.
3. We **prove** a sufficient-condition theorem that discharges the viability inequality:

`L_total(T,n,Zeff) < E · P_dep(T,n)` ,

using only checkable assumptions on:
- temperature regime (`T ≥ 1` and `η(T) ≤ 1`)
- density `n`
- enhancement factor `E`
- and calibrated coefficients in `PowerBalance.Params`.

This provides a fully formal bridge from:
“we have an enhancement factor E”
to
“net power is positive under an explicit, auditable model.”
-/

namespace IndisputableMonolith
namespace Fusion
namespace PowerBalanceBounds

open ReactionNetworkRates
open NuclearBridge
open Ignition

noncomputable section
set_option autoImplicit false

/-! ## Concrete deposited heating using the committed ⟨σv⟩ proxy -/

/-- Baseline deposited fusion heating proxy:

`P_dep(T,n) = f_dep · k_fus · n^2 · (T · exp(-η(T)))`.
-/
def Pdep_proxy (P : PowerBalance.Params) (g : GamowParams) (cfgA cfgB : NuclearConfig) (n : ℝ) : ℝ :=
  P.f_dep * (P.k_fus * (n ^ 2) * ReactivityProxy.sigmaV g cfgA cfgB)

/-! ## Helper bounds -/

private lemma sqrt_le_self_of_one_le {T : ℝ} (hT : 1 ≤ T) : Real.sqrt T ≤ T := by
  have hT0 : 0 ≤ T := le_trans (by norm_num : (0 : ℝ) ≤ 1) hT
  -- `Real.sqrt_le_left` gives: √T ≤ T ↔ T ≤ T^2 (since T ≥ 0)
  have hiff : (Real.sqrt T ≤ T) ↔ T ≤ T ^ 2 := by
    simpa using (Real.sqrt_le_left (x := T) (y := T) hT0)
  -- For T ≥ 1, T ≤ T^2.
  have hpow : T ≤ T ^ 2 := by
    nlinarith
  exact hiff.2 hpow

private lemma classicalTunneling_ge_exp_neg_one
    (g : GamowParams) (cfgA cfgB : NuclearConfig)
    (hη : gamowExponent g cfgA cfgB ≤ 1) :
    Real.exp (-1 : ℝ) ≤ classicalTunneling g cfgA cfgB := by
  -- classicalTunneling = exp(-η); if η ≤ 1 then -1 ≤ -η, hence exp(-1) ≤ exp(-η).
  unfold classicalTunneling
  have hneg : (-1 : ℝ) ≤ -gamowExponent g cfgA cfgB := by
    linarith
  exact (Real.exp_le_exp).2 hneg

/-! ## Main bound: discharge the viability inequality -/

/--
Sufficient condition (proved) for the concrete inequality

`L_total(T,n,Zeff) < E · Pdep_proxy(T,n)`

under the committed models.

Assumptions:
- `T ≥ 1` so that `√T ≤ T`
- `η(T) ≤ 1` so that `exp(-η(T)) ≥ exp(-1)` (a conservative but fully formal bound)
- `n > 0`
- `E ≥ 1`
- a simple “margin” inequality on parameters ensuring fusion dominates transport+brems.

This theorem is intentionally conservative; it is a *guaranteed* sufficient condition.
-/
theorem L_total_lt_E_Pdep_proxy
    (P : PowerBalance.Params)
    (g : GamowParams) (cfgA cfgB : NuclearConfig)
    (n Zeff E : ℝ)
    (hT : 1 ≤ g.temperature)
    (hη : gamowExponent g cfgA cfgB ≤ 1)
    (hn : 0 < n)
    (hZ : 0 ≤ Zeff)
    (hE : 1 ≤ E)
    (hMargin :
      P.k_tr * n < (E * P.f_dep * P.k_fus * Real.exp (-1) - P.k_brem * Zeff) * (n ^ 2)) :
    PowerBalance.L_total P g.temperature n Zeff < E * Pdep_proxy P g cfgA cfgB n := by
  have hn0 : 0 ≤ n := le_of_lt hn
  have hTpos : 0 < g.temperature := g.temperature_pos
  have hsqrt : Real.sqrt g.temperature ≤ g.temperature := sqrt_le_self_of_one_le hT
  have hTun : Real.exp (-1 : ℝ) ≤ classicalTunneling g cfgA cfgB :=
    classicalTunneling_ge_exp_neg_one g cfgA cfgB hη

  -- 1) Upper-bound loss by replacing √T with T (since T ≥ 1).
  have hLoss_le :
      PowerBalance.L_total P g.temperature n Zeff ≤
        (P.k_brem * Zeff * (n ^ 2) * g.temperature) + (P.k_tr * n * g.temperature) := by
    unfold PowerBalance.L_total PowerBalance.L_brem PowerBalance.L_tr
    -- L_brem term: ... * √T ≤ ... * T using `hsqrt` and nonnegativity.
    have hcoef_nonneg : 0 ≤ P.k_brem * Zeff * (n ^ 2) := by
      have hn2 : 0 ≤ n ^ 2 := by nlinarith [hn0]
      have : 0 ≤ P.k_brem * Zeff := mul_nonneg P.k_brem_nonneg hZ
      exact mul_nonneg this hn2
    have hbrem :
        P.k_brem * Zeff * (n ^ 2) * Real.sqrt g.temperature ≤
          P.k_brem * Zeff * (n ^ 2) * g.temperature := by
      exact mul_le_mul_of_nonneg_left hsqrt hcoef_nonneg
    -- Combine with the transport term.
    linarith

  -- 2) Combine: loss ≤ (brems+tr)·T,
  -- and use the supplied margin inequality to get strict `<` against the conservative
  -- fusion lower bound `(E f_dep k_fus e^{-1})·n^2·T`.
  -- and use the supplied margin inequality to get strict `<`.
  have hGoal_suff :
      (P.k_brem * Zeff * (n ^ 2) * g.temperature) + (P.k_tr * n * g.temperature) <
        (E * P.f_dep * P.k_fus * Real.exp (-1)) * (n ^ 2) * g.temperature := by
    -- Factor out `T > 0` and use the margin assumption.
    have hT0 : 0 < g.temperature := g.temperature_pos
    -- Rewrite the margin into the form we need.
    -- hMargin: k_tr*n < (E f_dep k_fus e^{-1} - k_brem*Zeff) * n^2
    -- Multiply both sides by T.
    have hMarginT :
        (P.k_tr * n) * g.temperature <
          ((E * P.f_dep * P.k_fus * Real.exp (-1) - P.k_brem * Zeff) * (n ^ 2)) * g.temperature := by
      exact mul_lt_mul_of_pos_right hMargin hT0
    -- Expand RHS and rearrange.
    -- Goal is: k_brem*Zeff*n^2*T + k_tr*n*T < (E f_dep k_fus e^{-1})*n^2*T
    -- which is equivalent to: k_tr*n*T < ((E f_dep k_fus e^{-1}) - k_brem*Zeff)*n^2*T
    -- exactly `hMarginT`.
    nlinarith [hMarginT]

  -- Finish: L_total ≤ ... < ... ≤ E*Pdep_proxy
  have hmid : PowerBalance.L_total P g.temperature n Zeff <
      (E * P.f_dep * P.k_fus * Real.exp (-1)) * (n ^ 2) * g.temperature := by
    exact lt_of_le_of_lt hLoss_le hGoal_suff
  -- Lower-bound `E * Pdep_proxy` using `exp(-η) ≥ exp(-1)`.
  have hbound_le :
      (E * P.f_dep * P.k_fus * Real.exp (-1)) * (n ^ 2) * g.temperature ≤
        E * Pdep_proxy P g cfgA cfgB n := by
    -- Start from `exp(-1) ≤ exp(-η)` and multiply by nonnegative scalars.
    have hTnonneg : 0 ≤ g.temperature := le_of_lt g.temperature_pos
    have hn2 : 0 ≤ n ^ 2 := by nlinarith [hn0]
    have hE0 : 0 ≤ E := le_trans (by norm_num : (0 : ℝ) ≤ 1) hE
    have hK0 : 0 ≤ E * P.f_dep * P.k_fus * (n ^ 2) * g.temperature := by
      have h1 : 0 ≤ E * P.f_dep := mul_nonneg hE0 P.f_dep_nonneg
      have h2 : 0 ≤ E * P.f_dep * P.k_fus := mul_nonneg h1 P.k_fus_nonneg
      have h3 : 0 ≤ E * P.f_dep * P.k_fus * (n ^ 2) := mul_nonneg h2 hn2
      exact mul_nonneg h3 hTnonneg
    -- Multiply `hTun` by `K := E*f_dep*k_fus*n^2*T ≥ 0`.
    have hmult :
        (E * P.f_dep * P.k_fus * (n ^ 2) * g.temperature) * Real.exp (-1) ≤
          (E * P.f_dep * P.k_fus * (n ^ 2) * g.temperature) * classicalTunneling g cfgA cfgB := by
      exact mul_le_mul_of_nonneg_left hTun hK0
    -- Rewrite RHS to the target expression.
    unfold Pdep_proxy ReactivityProxy.sigmaV
    -- normalize multiplications
    -- RHS: E * (f_dep * (k_fus * n^2 * (T * classicalTunneling))) = (E*f_dep*k_fus*n^2*T)*classicalTunneling
    -- LHS similarly matches the stated bound.
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmult

  exact lt_of_lt_of_le hmid hbound_le

end

end PowerBalanceBounds
end Fusion
end IndisputableMonolith
