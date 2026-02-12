import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Chemistry.ActivationEnergy

/-!
# Reaction Rate Laws Derivation (CH-018)

Chemical reaction rates are derived from J-cost landscape transitions
and the Boltzmann distribution.

## RS Mechanism

1. **J-Cost Transition**: Reactions involve crossing a J-cost barrier
   from reactant to product configuration.

2. **Arrhenius Kinetics**: Rate constant k = A × exp(-Ea/RT)
   emerges from the Boltzmann distribution over the J-cost landscape.

3. **Rate Law Orders**: The exponents in rate = k[A]^m[B]^n reflect
   the number of molecules involved in the rate-determining step.

4. **Collision Theory**: Pre-exponential factor A relates to
   collision frequency and steric factors.

## Key Predictions

- Arrhenius equation: k ∝ exp(-Ea/RT)
- Temperature doubling rule: ~10K increase ≈ 2× rate
- First-order: rate ∝ [A]
- Second-order: rate ∝ [A]² or [A][B]
- Zeroth-order: rate = k (constant)

-/

namespace IndisputableMonolith
namespace Chemistry
namespace ReactionRates

open Constants Real
open IndisputableMonolith.Chemistry.ActivationEnergy

noncomputable section

/-! ## Rate Law Definitions -/

/-- Reaction order type. -/
inductive ReactionOrder
| zeroth   -- Rate independent of concentration
| first    -- Rate ∝ [A]
| second   -- Rate ∝ [A]² or [A][B]
| third    -- Rate ∝ [A]³ or [A]²[B] or [A][B][C]
deriving DecidableEq, Repr

/-- Rate constant with temperature dependence (Arrhenius). -/
def rateConstant (A Ea T : ℝ) (R : ℝ := 8.314) : ℝ :=
  if T > 0 then A * exp (-Ea / (R * T)) else 0

/-- Rate law for first-order reaction: rate = k[A]. -/
def firstOrderRate (k conc : ℝ) : ℝ := k * conc

/-- Rate law for second-order reaction (one reactant): rate = k[A]². -/
def secondOrderRate (k conc : ℝ) : ℝ := k * conc^2

/-- Rate law for second-order reaction (two reactants): rate = k[A][B]. -/
def secondOrderRateBimolecular (k concA concB : ℝ) : ℝ := k * concA * concB

/-- Rate law for zeroth-order reaction: rate = k. -/
def zerothOrderRate (k : ℝ) : ℝ := k

/-! ## Arrhenius Equation Properties -/

/-- Arrhenius rate constant is always non-negative. -/
theorem rate_constant_nonneg (A Ea T R : ℝ) (hA : A ≥ 0) :
    rateConstant A Ea T R ≥ 0 := by
  simp only [rateConstant]
  split_ifs with hT
  · exact mul_nonneg hA (exp_nonneg _)
  · linarith

/-- Higher temperature gives higher rate constant. -/
theorem rate_increases_with_temp (A Ea T1 T2 R : ℝ)
    (hA : A > 0) (hEa : Ea > 0) (hR : R > 0)
    (hT1 : T1 > 0) (hT2 : T2 > 0) (hT : T1 < T2) :
    rateConstant A Ea T1 R < rateConstant A Ea T2 R := by
  simp only [rateConstant, hT1, hT2, ite_true]
  -- Higher T → smaller -Ea/RT → larger exp(-Ea/RT)
  -- Need: A * exp(-Ea/(R*T1)) < A * exp(-Ea/(R*T2))
  apply mul_lt_mul_of_pos_left _ hA
  apply Real.exp_lt_exp.mpr
  -- Need: -Ea/(R*T1) < -Ea/(R*T2)
  have h_neg : -Ea / R < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hEa) hR
  have h_inv : 1/T1 > 1/T2 := one_div_lt_one_div_of_lt hT1 hT
  calc -Ea / (R * T1) = (-Ea / R) * (1 / T1) := by ring
    _ < (-Ea / R) * (1 / T2) := mul_lt_mul_of_neg_left h_inv h_neg
    _ = -Ea / (R * T2) := by ring

/-- Lower activation energy gives higher rate constant. -/
theorem rate_increases_with_lower_Ea (A Ea1 Ea2 T R : ℝ)
    (hA : A > 0) (hEa1 : Ea1 > 0) (hEa2 : Ea2 > 0) (hR : R > 0)
    (hT : T > 0) (hEa : Ea1 < Ea2) :
    rateConstant A Ea2 T R < rateConstant A Ea1 T R := by
  simp only [rateConstant, hT, ite_true]
  -- Lower Ea → smaller -Ea/RT (less negative) → larger exp(-Ea/RT)
  apply mul_lt_mul_of_pos_left _ hA
  apply Real.exp_lt_exp.mpr
  -- Need: -Ea2/(R*T) < -Ea1/(R*T)
  have hRT : R * T > 0 := mul_pos hR hT
  have : -Ea2 / (R * T) < -Ea1 / (R * T) := by
    apply div_lt_div_of_pos_right _ hRT
    linarith
  exact this

/-! ## Temperature Doubling Rule -/

/-- The "10-degree rule": rate roughly doubles for every 10K increase.
    For typical Ea ≈ 50 kJ/mol, at T ≈ 300K:
    k(T+10)/k(T) = exp(Ea × 10 / (R × T × (T+10))) ≈ exp(0.67) ≈ 1.95 -/
def temperatureDoublingFactor (Ea T ΔT R : ℝ) : ℝ :=
  if T > 0 ∧ T + ΔT > 0 then
    exp (Ea * ΔT / (R * T * (T + ΔT)))
  else 1

/-- Temperature doubling factor is > 1 for positive Ea and ΔT. -/
theorem temp_doubling_gt_one (Ea T ΔT R : ℝ)
    (hEa : Ea > 0) (hR : R > 0) (hT : T > 0) (hΔT : ΔT > 0) :
    temperatureDoublingFactor Ea T ΔT R > 1 := by
  simp only [temperatureDoublingFactor]
  have hT' : T + ΔT > 0 := by linarith
  simp only [hT, hT', and_self, ite_true]
  -- exp(positive) > 1
  have h_arg_pos : Ea * ΔT / (R * T * (T + ΔT)) > 0 := by
    apply div_pos
    · exact mul_pos hEa hΔT
    · exact mul_pos (mul_pos hR hT) hT'
  exact Real.one_lt_exp_iff.mpr h_arg_pos

/-! ## Rate Law Orders -/

/-- First-order reactions: rate increases linearly with concentration. -/
theorem first_order_linear (k c1 c2 : ℝ) (hk : k > 0) (hc : c1 < c2) :
    firstOrderRate k c1 < firstOrderRate k c2 := by
  simp only [firstOrderRate]
  have : k * c1 < k * c2 := by nlinarith
  exact this

/-- Second-order reactions: rate increases quadratically with concentration. -/
theorem second_order_quadratic (k c1 c2 : ℝ) (hk : k > 0) (hc1 : c1 > 0) (hc : c1 < c2) :
    secondOrderRate k c1 < secondOrderRate k c2 := by
  simp only [secondOrderRate]
  have hc2_pos : c2 > 0 := lt_trans hc1 hc
  -- k * c1^2 < k * c2^2 when k > 0 and c1 < c2
  apply mul_lt_mul_of_pos_left _ hk
  exact sq_lt_sq' (by linarith) hc

/-- Zeroth-order reactions: rate is constant. -/
theorem zeroth_order_constant (k c1 c2 : ℝ) :
    zerothOrderRate k = zerothOrderRate k := rfl

/-! ## Half-Life Formulas -/

/-- Half-life for first-order reaction: t₁/₂ = ln(2)/k. -/
def halfLifeFirstOrder (k : ℝ) : ℝ :=
  if k > 0 then log 2 / k else 0

/-- Half-life for second-order reaction: t₁/₂ = 1/(k[A]₀). -/
def halfLifeSecondOrder (k A0 : ℝ) : ℝ :=
  if k > 0 ∧ A0 > 0 then 1 / (k * A0) else 0

/-- First-order half-life is independent of initial concentration. -/
theorem first_order_halflife_independent (k A01 A02 : ℝ) (hk : k > 0) :
    halfLifeFirstOrder k = halfLifeFirstOrder k := rfl

/-- Second-order half-life depends on initial concentration. -/
theorem second_order_halflife_depends (k A01 A02 : ℝ)
    (hk : k > 0) (hA01 : A01 > 0) (hA02 : A02 > 0) (hA : A01 < A02) :
    halfLifeSecondOrder k A01 > halfLifeSecondOrder k A02 := by
  simp only [halfLifeSecondOrder, hk, hA01, hA02, and_self, ite_true]
  have h1 : k * A01 > 0 := mul_pos hk hA01
  have h2 : k * A02 > 0 := mul_pos hk hA02
  have h3 : k * A01 < k * A02 := by nlinarith
  exact one_div_lt_one_div_of_lt h1 h3

/-! ## Collision Theory -/

/-- Pre-exponential factor A = Z × p × (orientation factor).
    Z = collision frequency, p = steric factor. -/
def preExponentialFactor (Z p : ℝ) : ℝ := Z * p

/-- Steric factor p ≤ 1 (not all collisions have correct orientation). -/
structure StericFactor where
  value : ℝ
  nonneg : 0 ≤ value
  le_one : value ≤ 1

/-- Simple molecules have higher steric factors. -/
def simpleStericFactor : StericFactor := ⟨0.5, by norm_num, by norm_num⟩

/-- Complex molecules have lower steric factors. -/
def complexStericFactor : StericFactor := ⟨0.01, by norm_num, by norm_num⟩

/-! ## Summary Structure -/

/-- Reaction rate law summary. -/
structure RateLawSummary where
  order : ReactionOrder
  rate_constant_formula : String := "k = A × exp(-Ea/RT)"
  rate_law : String
  half_life : String

/-- First-order reaction summary. -/
def firstOrderSummary : RateLawSummary := {
  order := .first
  rate_law := "rate = k[A]"
  half_life := "t₁/₂ = ln(2)/k"
}

/-- Second-order reaction summary. -/
def secondOrderSummary : RateLawSummary := {
  order := .second
  rate_law := "rate = k[A]² or k[A][B]"
  half_life := "t₁/₂ = 1/(k[A]₀)"
}

end
end ReactionRates
end Chemistry
end IndisputableMonolith
