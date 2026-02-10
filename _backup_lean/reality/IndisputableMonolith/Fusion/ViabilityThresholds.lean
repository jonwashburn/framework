import IndisputableMonolith.Fusion.PowerBalanceBounds

/-!
# Solvable Thresholds (T* and E*) for Viability

This module removes the ad‑hoc regime assumptions used in `Fusion.PowerBalanceBounds`:

- `T ≥ 1`
- `η(T) ≤ 1`

and replaces them with **explicit solvable thresholds** derived from:

1. the closed-form Gamow exponent proxy
2. the concrete loss/heating models

We prove a final statement of the requested form:

> If `T ≥ T*` and `E ≥ E*`, then viability holds (under the committed proxy models).
-/

namespace IndisputableMonolith
namespace Fusion
namespace ViabilityThresholds

open ReactionNetworkRates
open NuclearBridge
open Ignition

noncomputable section
set_option autoImplicit false

/-! ## Temperature threshold T* from the Gamow exponent formula -/

/--
Numerator (“Gamow coefficient”) in the simplified exponent:

`η(T) = gamowCoeff / √T`
-/
def gamowCoeff (cfgA cfgB : NuclearConfig) : ℝ :=
  31.3 * (cfgA.Z : ℝ) * (cfgB.Z : ℝ) * Real.sqrt (reducedMass cfgA cfgB)

lemma gamowExponent_eq_coeff_div_sqrt (g : GamowParams) (cfgA cfgB : NuclearConfig) :
    gamowExponent g cfgA cfgB = gamowCoeff cfgA cfgB / Real.sqrt g.temperature := by
  unfold ReactionNetworkRates.gamowExponent gamowCoeff
  -- unfold the `let`s and normalize division
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/--
Explicit solvable temperature threshold:

`T* = max 1 (gamowCoeff^2)`

So `T ≥ T*` implies both:
- `T ≥ 1`
- `gamowExponent(T) ≤ 1`  (proved below)
-/
def T_star (cfgA cfgB : NuclearConfig) : ℝ :=
  max 1 ((gamowCoeff cfgA cfgB) ^ 2)

lemma one_le_T_star (cfgA cfgB : NuclearConfig) : (1 : ℝ) ≤ T_star cfgA cfgB := by
  simp [T_star]

lemma T_star_pos (cfgA cfgB : NuclearConfig) : 0 < T_star cfgA cfgB := by
  have h1 : (0 : ℝ) < 1 := by norm_num
  exact lt_of_lt_of_le h1 (one_le_T_star cfgA cfgB)

lemma one_le_of_T_ge_T_star (cfgA cfgB : NuclearConfig) (T : ℝ)
    (hT : T_star cfgA cfgB ≤ T) : (1 : ℝ) ≤ T := by
  exact le_trans (one_le_T_star cfgA cfgB) hT

lemma T_pos_of_T_ge_T_star (cfgA cfgB : NuclearConfig) (T : ℝ)
    (hT : T_star cfgA cfgB ≤ T) : 0 < T := by
  exact lt_of_lt_of_le (T_star_pos cfgA cfgB) hT

/--
If `T ≥ T_star(cfgA,cfgB)`, then `gamowExponent(T) ≤ 1`.

This is an *algebraic consequence* of the closed form
`η(T) = gamowCoeff / √T`.
-/
theorem gamowExponent_le_one_of_T_ge_T_star
    (cfgA cfgB : NuclearConfig) (T : ℝ)
    (hT : T_star cfgA cfgB ≤ T) :
    let g : GamowParams := ⟨T, T_pos_of_T_ge_T_star cfgA cfgB T hT⟩
    gamowExponent g cfgA cfgB ≤ 1 := by
  intro g
  -- From `T_star ≤ T`, we have `(gamowCoeff)^2 ≤ T`.
  have hpow : (gamowCoeff cfgA cfgB) ^ 2 ≤ T := by
    have : (gamowCoeff cfgA cfgB) ^ 2 ≤ T_star cfgA cfgB := by
      -- right component ≤ max
      exact le_max_right _ _
    exact le_trans this hT
  -- Hence `gamowCoeff ≤ √T`.
  have hle_sqrt : gamowCoeff cfgA cfgB ≤ Real.sqrt T := by
    -- `Real.le_sqrt_of_sq_le` turns `x^2 ≤ y` into `x ≤ √y`.
    simpa using (Real.le_sqrt_of_sq_le hpow)
  -- Divide by positive `√T`.
  have hsqrt_pos : 0 < Real.sqrt T := by
    exact (Real.sqrt_pos).2 (T_pos_of_T_ge_T_star cfgA cfgB T hT)
  have hsqrt_nonneg : 0 ≤ Real.sqrt T := le_of_lt hsqrt_pos
  have hdiv : (gamowCoeff cfgA cfgB) / Real.sqrt T ≤ (Real.sqrt T) / Real.sqrt T :=
    div_le_div_of_nonneg_right hle_sqrt hsqrt_nonneg
  have hsqrt_ne : Real.sqrt T ≠ 0 := ne_of_gt hsqrt_pos
  have : (gamowCoeff cfgA cfgB) / Real.sqrt T ≤ 1 := by
    simpa [div_self hsqrt_ne] using hdiv
  -- Rewrite `gamowExponent` into the `gamowCoeff/√T` form.
  simpa [gamowExponent_eq_coeff_div_sqrt (g := g) (cfgA := cfgA) (cfgB := cfgB)] using this

/-! ## Enhancement threshold E* from the margin inequality -/

private def A (P : PowerBalance.Params) : ℝ :=
  P.f_dep * P.k_fus * Real.exp (-1)

/--
Explicit enhancement threshold:

Let `A = f_dep * k_fus * exp(-1)`.

Define:
`E* = (k_brem*Zeff + k_tr/n)/A + 1`.

Then `E ≥ E*` implies the strict margin inequality used in
`PowerBalanceBounds.L_total_lt_E_Pdep_proxy`.
-/
def E_star (P : PowerBalance.Params) (n Zeff : ℝ) : ℝ :=
  ((P.k_brem * Zeff) + (P.k_tr / n)) / A P + 1

lemma A_pos_of_params (P : PowerBalance.Params) (h_fdep : 0 < P.f_dep) (h_kfus : 0 < P.k_fus) :
    0 < A P := by
  unfold A
  have hexp : 0 < Real.exp (-1 : ℝ) := Real.exp_pos _
  have : 0 < P.f_dep * P.k_fus := mul_pos h_fdep h_kfus
  exact mul_pos this hexp

lemma one_le_E_star (P : PowerBalance.Params) (n Zeff : ℝ)
    (hn : 0 < n) (hZ : 0 ≤ Zeff) (hA : 0 < A P) : (1 : ℝ) ≤ E_star P n Zeff := by
  unfold E_star
  have hn0 : 0 ≤ n := le_of_lt hn
  have htr_div_nonneg : 0 ≤ P.k_tr / n := by
    exact div_nonneg P.k_tr_nonneg hn0
  have hbrem_nonneg : 0 ≤ P.k_brem * Zeff := mul_nonneg P.k_brem_nonneg hZ
  have hsum_nonneg : 0 ≤ (P.k_brem * Zeff) + (P.k_tr / n) := add_nonneg hbrem_nonneg htr_div_nonneg
  have hfrac_nonneg : 0 ≤ ((P.k_brem * Zeff) + (P.k_tr / n)) / A P := by
    exact div_nonneg hsum_nonneg (le_of_lt hA)
  linarith

/--
`E ≥ E_star` implies the strict margin inequality:

`k_tr*n < (E*f_dep*k_fus*exp(-1) - k_brem*Zeff) * n^2`
-/
theorem margin_of_E_ge_E_star
    (P : PowerBalance.Params) (n Zeff E : ℝ)
    (hn : 0 < n) (_hZ : 0 ≤ Zeff)
    (h_fdep : 0 < P.f_dep) (h_kfus : 0 < P.k_fus)
    (hE : E_star P n Zeff ≤ E) :
    P.k_tr * n < (E * P.f_dep * P.k_fus * Real.exp (-1) - P.k_brem * Zeff) * (n ^ 2) := by
  have hA : 0 < A P := A_pos_of_params P h_fdep h_kfus
  have hn2_pos : 0 < n ^ 2 := by nlinarith [hn]

  -- From `E ≥ E_star`, multiply by positive `A` to compare `E*A`.
  have hmul : E * A P ≥ (E_star P n Zeff) * A P :=
    mul_le_mul_of_nonneg_right hE (le_of_lt hA)

  -- Compute `(E_star)*A = (k_brem*Zeff + k_tr/n) + A`.
  have hEstarA :
      (E_star P n Zeff) * A P = (P.k_brem * Zeff) + (P.k_tr / n) + A P := by
    unfold E_star
    field_simp [A, (ne_of_gt hA)]
    -- `field_simp` closes this goal in this setting.

  -- So `E*A ≥ k_brem*Zeff + k_tr/n + A`, hence `E*A - k_brem*Zeff > k_tr/n`.
  have hEA_ge :
      E * A P ≥ (P.k_brem * Zeff) + (P.k_tr / n) + A P := by
    -- Use the exact evaluation of `E_star*A`:
    have h1 : (E_star P n Zeff) * A P ≤ E * A P := by
      -- from `hmul` but with sides aligned
      simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using hmul
    -- Replace `(E_star)*A` by the explicit expression
    simpa [hEstarA] using h1

  have hstrict : (P.k_tr / n) < E * A P - (P.k_brem * Zeff) := by
    -- From `E*A ≥ k_brem*Zeff + k_tr/n + A` we get:
    -- `E*A - k_brem*Zeff ≥ k_tr/n + A > k_tr/n`.
    have h_ge : (P.k_tr / n) + A P ≤ E * A P - (P.k_brem * Zeff) := by
      linarith
    have hApos : 0 < A P := hA
    have : (P.k_tr / n) < (P.k_tr / n) + A P := by linarith
    exact lt_of_lt_of_le this h_ge

  -- Multiply by `n^2` (positive) and rewrite `A`.
  have hmult2 :
      (P.k_tr / n) * (n ^ 2) < (E * A P - (P.k_brem * Zeff)) * (n ^ 2) :=
    mul_lt_mul_of_pos_right hstrict hn2_pos

  -- Simplify LHS: (k_tr/n)*n^2 = k_tr*n
  have hn_ne : n ≠ 0 := ne_of_gt hn
  have hLHS : (P.k_tr / n) * (n ^ 2) = P.k_tr * n := by
    -- (k_tr / n) * n^2 = k_tr * (n^2 / n) = k_tr * n
    field_simp [hn_ne]
    -- `field_simp` closes this goal in this setting.

  -- Rewrite RHS: E*A = E*f_dep*k_fus*exp(-1)
  have hRHS :
      (E * A P - (P.k_brem * Zeff)) * (n ^ 2) =
        (E * P.f_dep * P.k_fus * Real.exp (-1) - P.k_brem * Zeff) * (n ^ 2) := by
    -- Expand `A` and normalize multiplication order.
    simp [A, mul_assoc, mul_left_comm, mul_comm]
  -- Finish
  simpa [hLHS, hRHS] using hmult2

/-! ## Final theorem: viability from T ≥ T* and E ≥ E* -/

/--
Final theorem (requested form):

If `T ≥ T*` and `E ≥ E*`, then the **concrete viability inequality** holds:

`L_total(T,n,Zeff) < E · Pdep_proxy(T,n)`.

This is a *model-layer* guarantee: it is true for the chosen proxy models, and therefore
the simulator can produce certificates for it once the parameter instantiations are supplied.
-/
theorem viable_of_T_ge_T_star_and_E_ge_E_star
    (P : PowerBalance.Params)
    (cfgA cfgB : NuclearConfig)
    (T n Zeff E : ℝ)
    (hT : T_star cfgA cfgB ≤ T)
    (hn : 0 < n) (hZ : 0 ≤ Zeff)
    (h_fdep : 0 < P.f_dep) (h_kfus : 0 < P.k_fus)
    (hE : E_star P n Zeff ≤ E) :
    viable (fun _ => E * PowerBalanceBounds.Pdep_proxy P ⟨T, T_pos_of_T_ge_T_star cfgA cfgB T hT⟩ cfgA cfgB n)
      (fun _ => PowerBalance.L_total P T n Zeff) T := by
  -- Build the Gamow params from T and derive the two old regime assumptions.
  let g : GamowParams := ⟨T, T_pos_of_T_ge_T_star cfgA cfgB T hT⟩
  have hT1 : (1 : ℝ) ≤ g.temperature := by
    -- g.temperature = T
    simpa [g] using one_le_of_T_ge_T_star cfgA cfgB T hT
  have hη : gamowExponent g cfgA cfgB ≤ 1 := by
    simpa [g] using gamowExponent_le_one_of_T_ge_T_star cfgA cfgB T hT
  have hMargin :
      P.k_tr * n < (E * P.f_dep * P.k_fus * Real.exp (-1) - P.k_brem * Zeff) * (n ^ 2) := by
    exact margin_of_E_ge_E_star P n Zeff E hn hZ h_fdep h_kfus hE
  have hineq :
      PowerBalance.L_total P g.temperature n Zeff <
        E * PowerBalanceBounds.Pdep_proxy P g cfgA cfgB n :=
    PowerBalanceBounds.L_total_lt_E_Pdep_proxy P g cfgA cfgB n Zeff E hT1 hη hn hZ (by
      have : (1 : ℝ) ≤ E := le_trans (one_le_E_star P n Zeff hn hZ (A_pos_of_params P h_fdep h_kfus)) hE
      exact this) hMargin
  -- Convert inequality to `viable`.
  unfold viable
  simpa [g] using hineq

end

end ViabilityThresholds
end Fusion
end IndisputableMonolith
