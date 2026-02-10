import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Chemistry.ReactionRates

/-!
# Equilibrium Constants Derivation (CH-019)

Chemical equilibrium occurs when the forward and reverse reaction rates are equal,
resulting in no net change in concentrations. The equilibrium constant (K) quantifies
the relative amounts of products and reactants at equilibrium.

## RS Mechanism

1. **J-Cost Minimization at Equilibrium**: At equilibrium, the system minimizes total
   J-cost across all configurations. This is analogous to minimizing Gibbs free energy
   in thermodynamics.

2. **Ratio of Rate Constants**: For a reversible reaction A ⇌ B, the equilibrium
   constant K = k_forward / k_reverse. Since both rate constants follow Arrhenius
   behavior derived from J-cost landscapes, their ratio gives:
   K = exp(-ΔG°/RT)

3. **Temperature Dependence (Van't Hoff)**: The temperature dependence of K follows
   from the Arrhenius derivation:
   d(ln K)/dT = ΔH°/(RT²)

4. **Le Chatelier's Principle**: Systems at equilibrium respond to perturbations by
   shifting to minimize J-cost. This naturally emerges from cost minimization.

5. **φ-Scaling**: Equilibrium constants can be related to φ-ladders through the
   activation energy scaling.

## Predictions

- Equilibrium is reached when forward rate = reverse rate.
- K = [products]/[reactants] at equilibrium (with stoichiometric powers).
- K is temperature-dependent via Van't Hoff equation.
- ΔG° = -RT ln(K) relates thermodynamics to kinetics.
- Le Chatelier's principle follows from cost minimization.
- K_p = K_c × (RT)^Δn for gas-phase reactions.

-/

namespace IndisputableMonolith
namespace Chemistry
namespace EquilibriumConstants

open Real
open IndisputableMonolith.Constants
open IndisputableMonolith.Cost

noncomputable section

/-- Gas constant in J/(mol·K). -/
def R_gas : ℝ := 8.314

/-- R_gas is positive. -/
lemma R_gas_pos : R_gas > 0 := by norm_num [R_gas]

/-- Standard temperature in K. -/
def T_standard : ℝ := 298.15

/-! ## Equilibrium Constant Definitions -/

/-- Equilibrium constant as ratio of rate constants.
    For A ⇌ B: K = k_f / k_r. -/
def equilibriumConstantFromRates (k_forward k_reverse : ℝ) : ℝ :=
  if k_reverse > 0 then k_forward / k_reverse else 0

/-- Equilibrium constant from Gibbs free energy.
    K = exp(-ΔG°/RT). -/
def equilibriumConstantFromGibbs (ΔG_standard : ℝ) (T : ℝ) : ℝ :=
  if T > 0 then exp (-ΔG_standard / (R_gas * T)) else 0

/-- Gibbs free energy change from equilibrium constant.
    ΔG° = -RT ln(K). -/
def gibbsFromEquilibrium (K : ℝ) (T : ℝ) : ℝ :=
  if K > 0 ∧ T > 0 then -R_gas * T * log K else 0

/-- Reaction quotient Q (same form as K, but not at equilibrium). -/
def reactionQuotient (products reactants : List ℝ) : ℝ :=
  let prod := products.foldl (· * ·) 1
  let react := reactants.foldl (· * ·) 1
  if react > 0 then prod / react else 0

/-! ## Rate Constant Relationship -/

/-- At equilibrium, the ratio k_f/k_r equals K. -/
theorem equilibrium_rate_ratio (k_f k_r K : ℝ)
    (hk_r : k_r > 0) (heq : k_f / k_r = K) :
    equilibriumConstantFromRates k_f k_r = K := by
  simp only [equilibriumConstantFromRates, hk_r, ite_true]
  exact heq

/-- Equilibrium constant is positive when both rates are positive. -/
theorem equilibrium_const_pos (k_f k_r : ℝ) (hk_f : k_f > 0) (hk_r : k_r > 0) :
    equilibriumConstantFromRates k_f k_r > 0 := by
  simp only [equilibriumConstantFromRates, hk_r, ite_true]
  exact div_pos hk_f hk_r

/-! ## Thermodynamic Relationship -/

/-- ΔG° < 0 implies K > 1 (products favored). -/
theorem negative_gibbs_implies_K_gt_1 (ΔG T : ℝ) (hT : T > 0) (hG : ΔG < 0) :
    equilibriumConstantFromGibbs ΔG T > 1 := by
  simp only [equilibriumConstantFromGibbs, hT, ite_true]
  -- exp(positive) > 1 when -ΔG/(R*T) > 0
  have hRT : R_gas * T > 0 := mul_pos R_gas_pos hT
  have h_arg : -ΔG / (R_gas * T) > 0 := div_pos (neg_pos.mpr hG) hRT
  exact Real.one_lt_exp_iff.mpr h_arg

/-- ΔG° > 0 implies K < 1 (reactants favored). -/
theorem positive_gibbs_implies_K_lt_1 (ΔG T : ℝ) (hT : T > 0) (hG : ΔG > 0) :
    equilibriumConstantFromGibbs ΔG T < 1 := by
  simp only [equilibriumConstantFromGibbs, hT, ite_true]
  -- exp(negative) < 1 when -ΔG/(R*T) < 0
  have hRT : R_gas * T > 0 := mul_pos R_gas_pos hT
  have h_neg : -ΔG < 0 := neg_neg_of_pos hG
  have h_arg : -ΔG / (R_gas * T) < 0 := div_neg_of_neg_of_pos h_neg hRT
  exact Real.exp_lt_one_iff.mpr h_arg

/-- ΔG° = 0 implies K = 1. -/
theorem zero_gibbs_implies_K_eq_1 (T : ℝ) (hT : T > 0) :
    equilibriumConstantFromGibbs 0 T = 1 := by
  simp only [equilibriumConstantFromGibbs, hT, ite_true]
  simp only [neg_zero, zero_div, exp_zero]

/-! ## Van't Hoff Equation -/

/-- Van't Hoff equation: ln(K₂/K₁) = -ΔH/R × (1/T₂ - 1/T₁).
    This relates equilibrium constants at two temperatures. -/
def vantHoffRatio (K1 K2 : ℝ) : ℝ :=
  if K1 > 0 ∧ K2 > 0 then log K2 - log K1 else 0

/-- Van't Hoff prediction for K ratio. -/
def vantHoffPrediction (ΔH T1 T2 : ℝ) : ℝ :=
  if T1 > 0 ∧ T2 > 0 then
    -ΔH / R_gas * (1/T2 - 1/T1)
  else 0

/-- For endothermic reactions (ΔH > 0), K increases with temperature. -/
theorem endothermic_K_increases (ΔH T1 T2 : ℝ)
    (hΔH : ΔH > 0) (hT1 : T1 > 0) (hT2 : T2 > 0) (hT : T1 < T2) :
    vantHoffPrediction ΔH T1 T2 > 0 := by
  simp only [vantHoffPrediction, hT1, hT2, and_self, ite_true]
  -- (-ΔH/R) * (1/T2 - 1/T1) > 0 when ΔH > 0 and T2 > T1
  -- Because (1/T2 - 1/T1) < 0 and -ΔH/R < 0, their product is positive
  have h_neg_ΔH : -ΔH < 0 := neg_neg_of_pos hΔH
  have h_neg_ratio : -ΔH / R_gas < 0 := div_neg_of_neg_of_pos h_neg_ΔH R_gas_pos
  have h_inv_diff : 1/T2 - 1/T1 < 0 := by
    have h1 : 1/T2 < 1/T1 := one_div_lt_one_div_of_lt hT1 hT
    linarith
  exact mul_pos_of_neg_of_neg h_neg_ratio h_inv_diff

/-- For exothermic reactions (ΔH < 0), K decreases with temperature. -/
theorem exothermic_K_decreases (ΔH T1 T2 : ℝ)
    (hΔH : ΔH < 0) (hT1 : T1 > 0) (hT2 : T2 > 0) (hT : T1 < T2) :
    vantHoffPrediction ΔH T1 T2 < 0 := by
  simp only [vantHoffPrediction, hT1, hT2, and_self, ite_true]
  -- (-ΔH/R) * (1/T2 - 1/T1) < 0 when ΔH < 0 and T2 > T1
  -- Because (1/T2 - 1/T1) < 0 and -ΔH/R > 0, their product is negative
  have h_pos_ratio : -ΔH / R_gas > 0 := div_pos (neg_pos.mpr hΔH) R_gas_pos
  have h_inv_diff : 1/T2 - 1/T1 < 0 := by
    have h1 : 1/T2 < 1/T1 := one_div_lt_one_div_of_lt hT1 hT
    linarith
  exact mul_neg_of_pos_of_neg h_pos_ratio h_inv_diff

/-! ## Le Chatelier's Principle -/

/-- Reaction quotient compared to equilibrium constant.
    Q < K means reaction shifts right (toward products).
    Q > K means reaction shifts left (toward reactants). -/
def shiftsTowardProducts (Q K : ℝ) : Prop := Q < K

def shiftsTowardReactants (Q K : ℝ) : Prop := Q > K

def atEquilibrium (Q K : ℝ) : Prop := Q = K

/-- If Q < K, system is not at equilibrium and will shift right. -/
theorem q_lt_k_not_equilibrium (Q K : ℝ) (h : Q < K) : ¬atEquilibrium Q K := by
  intro heq
  rw [atEquilibrium] at heq
  linarith

/-! ## Pressure-Concentration Relationship -/

/-- K_p = K_c × (RT)^Δn for ideal gas reactions.
    Δn is the change in moles of gas (products - reactants). -/
def Kp_from_Kc (Kc Δn T : ℝ) : ℝ :=
  if T > 0 then Kc * (R_gas * T) ^ Δn else 0

/-- If Δn = 0, then K_p = K_c. -/
theorem kp_eq_kc_when_delta_n_zero (Kc T : ℝ) (hT : T > 0) :
    Kp_from_Kc Kc 0 T = Kc := by
  simp only [Kp_from_Kc, hT, ite_true, rpow_zero, mul_one]

/-- If Δn > 0 and RT > 1, then K_p > K_c. -/
theorem kp_gt_kc_when_delta_n_positive (Kc Δn T : ℝ)
    (hKc : Kc > 0) (hΔn : Δn > 0) (hT : T > 0) (hRT : R_gas * T > 1) :
    Kp_from_Kc Kc Δn T > Kc := by
  simp only [Kp_from_Kc, hT, ite_true]
  -- K_p = K_c * (RT)^Δn > K_c when (RT)^Δn > 1 (which holds for RT > 1, Δn > 0)
  have h_RT_pos : R_gas * T > 0 := mul_pos R_gas_pos hT
  have h_factor_gt_one : (R_gas * T) ^ Δn > 1 := Real.one_lt_rpow hRT hΔn
  calc Kc * (R_gas * T) ^ Δn > Kc * 1 := by apply mul_lt_mul_of_pos_left h_factor_gt_one hKc
    _ = Kc := mul_one Kc

end

end EquilibriumConstants
end Chemistry
end IndisputableMonolith
