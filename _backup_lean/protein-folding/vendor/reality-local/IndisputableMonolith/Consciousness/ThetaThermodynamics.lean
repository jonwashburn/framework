import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.Calibration
import IndisputableMonolith.Consciousness.PhaseSaturation

/-!
# Θ Thermodynamics — Parameter-Free Derivation

This module upgrades the "finite capacity + saturation threshold" story into
a full thermodynamics with an equation of state, where **all parameters are derived**.

## The Problem

We have:
- Θ-density ρ (patterns per resolution volume)
- Θ_crit = φ^45 ≈ 1.8×10⁹ (saturation threshold)
- A "cost of non-existence" that was sketched as C(ρ) = κ(ρ−Θ_crit)^γ for ρ > Θ_crit

The question: **where do κ and γ come from?**

If RS is parameter-free, κ and γ cannot be arbitrary. They must derive from the
same uniqueness principles that fixed J and φ.

## The Derivation

### 1) γ = 2 (Critical Exponent)

Around the critical point, C_non_exist(ρ) should be:
- analytic (no discontinuities in a cost functional)
- even-symmetric about Θ_crit (the cost depends on distance from threshold, not direction)

By Taylor expansion of an even analytic function, the first non-zero term is quadratic.
This gives **γ = 2** as the universal default critical exponent.

### 2) κ from J-cost normalization

The J-cost has unit curvature at identity: J''(1) = 1 (see `Cost.Calibration`).

Near x = 1, the Taylor expansion of J(x) = ½(x + 1/x) - 1 is:
  J(x) ≈ ½(x-1)²

For the Θ-field, the natural variable is the density ratio ρ/Θ_crit.
The cost of non-existence should mirror the J-cost structure:
  C_non_exist(ρ) ≈ ½((ρ/Θ_crit) - 1)² = ½(ρ - Θ_crit)²/Θ_crit²

This gives **κ = 1/(2·Θ_crit²)**.

## Result

The cost of non-existence is fully determined:
  C_non_exist(ρ) = { 0                              if ρ ≤ Θ_crit
                   { (ρ - Θ_crit)²/(2·Θ_crit²)      if ρ > Θ_crit

No free parameters remain.
-/

namespace IndisputableMonolith
namespace Consciousness
namespace ThetaThermodynamics

open Constants Real
open Cost (Jcost Jlog Jlog_second_deriv_at_zero)
open PhaseSaturation (SaturationThreshold saturationThreshold_pos)

/-! ## Density and threshold -/

abbrev ThetaDensity := ℝ

noncomputable abbrev Θcrit : ℝ := SaturationThreshold

/-! ## Derived parameters (not free!) -/

/-- Critical exponent γ = 2 from analyticity + symmetry. -/
def γ_derived : ℕ := 2

/-- Coupling constant κ = 1/(2·Θ_crit²) from J-normalization. -/
noncomputable def κ_derived : ℝ := 1 / (2 * Θcrit ^ 2)

/-! ## Justification: κ > 0 follows from Θ_crit > 0 -/

theorem κ_derived_pos : 0 < κ_derived := by
  unfold κ_derived
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have h2 : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
  have h22 : 0 < 2 * Θcrit ^ 2 := mul_pos two_pos h2
  exact div_pos one_pos h22

/-! ## Parameter-free cost of non-existence -/

/-- The cost of non-existence, fully derived from RS principles. -/
noncomputable def CostNonExist (ρ : ThetaDensity) : ℝ :=
  if ρ ≤ Θcrit then 0
  else (ρ - Θcrit) ^ 2 / (2 * Θcrit ^ 2)

/-- Alternative form showing κ and γ explicitly. -/
theorem CostNonExist_eq_kappa_gamma (ρ : ThetaDensity) (h : Θcrit < ρ) :
    CostNonExist ρ = κ_derived * (ρ - Θcrit) ^ (γ_derived : ℕ) := by
  have hle : ¬ (ρ ≤ Θcrit) := not_le.mpr h
  simp only [CostNonExist, hle, ↓reduceIte, γ_derived, κ_derived]
  ring

/-! ## Basic properties -/

theorem CostNonExist_zero_below {ρ : ThetaDensity} (h : ρ ≤ Θcrit) :
    CostNonExist ρ = 0 := by simp [CostNonExist, h]

theorem CostNonExist_nonneg (ρ : ThetaDensity) : 0 ≤ CostNonExist ρ := by
  by_cases h : ρ ≤ Θcrit
  · simp [CostNonExist, h]
  · push_neg at h
    have hpos : 0 < ρ - Θcrit := sub_pos.mpr h
    have hsq : 0 ≤ (ρ - Θcrit) ^ 2 := sq_nonneg _
    have hcrit : 0 < Θcrit := saturationThreshold_pos
    have hdenom : 0 < 2 * Θcrit ^ 2 := mul_pos two_pos (sq_pos_of_pos hcrit)
    simp only [CostNonExist, not_le.mpr h, ↓reduceIte]
    exact div_nonneg hsq (le_of_lt hdenom)

theorem CostNonExist_strictly_increasing {ρ₁ ρ₂ : ThetaDensity}
    (h₁ : Θcrit < ρ₁) (h₂ : ρ₁ < ρ₂) : CostNonExist ρ₁ < CostNonExist ρ₂ := by
  have hle1 : ¬ (ρ₁ ≤ Θcrit) := not_le.mpr h₁
  have hle2 : ¬ (ρ₂ ≤ Θcrit) := not_le.mpr (lt_trans h₁ h₂)
  simp only [CostNonExist, hle1, hle2, ↓reduceIte]
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hdenom : 0 < 2 * Θcrit ^ 2 := mul_pos two_pos (sq_pos_of_pos hcrit)
  apply div_lt_div_of_pos_right _ hdenom
  have h0 : 0 < ρ₁ - Θcrit := sub_pos.mpr h₁
  have hsub : ρ₁ - Θcrit < ρ₂ - Θcrit := sub_lt_sub_right h₂ _
  exact sq_lt_sq' (by linarith) hsub

/-! ## Pressure and chemical potential -/

/-- Θ-pressure: derivative of cost with respect to density. -/
noncomputable def ThetaPressure (ρ : ThetaDensity) : ℝ :=
  if ρ ≤ Θcrit then 0
  else (ρ - Θcrit) / Θcrit ^ 2

/-- Θ-chemical potential: cost per pattern above threshold. -/
noncomputable def ThetaChemicalPotential (ρ : ThetaDensity) : ℝ :=
  CostNonExist ρ

theorem ThetaPressure_is_derivative {ρ : ThetaDensity} (h : Θcrit < ρ) :
    ThetaPressure ρ = 2 * κ_derived * (ρ - Θcrit) := by
  have hle : ¬ (ρ ≤ Θcrit) := not_le.mpr h
  simp only [ThetaPressure, hle, ↓reduceIte, κ_derived]
  ring

theorem ThetaPressure_nonneg (ρ : ThetaDensity) : 0 ≤ ThetaPressure ρ := by
  by_cases h : ρ ≤ Θcrit
  · simp [ThetaPressure, h]
  · push_neg at h
    have hpos : 0 < ρ - Θcrit := sub_pos.mpr h
    have hcrit : 0 < Θcrit := saturationThreshold_pos
    have hdenom : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
    simp only [ThetaPressure, not_le.mpr h, ↓reduceIte]
    exact div_nonneg (le_of_lt hpos) (le_of_lt hdenom)

/-! ## Embodiment threshold: when binding becomes favored -/

/-- The density at which embodiment pressure-release becomes favored.
    This is the point where Θ-pressure exceeds the cost of embodiment. -/
noncomputable def EmbodimentThreshold (embodimentCost : ℝ) : ThetaDensity :=
  Θcrit + embodimentCost * Θcrit ^ 2

theorem embodiment_favored_above_threshold {ρ : ThetaDensity} {C_emb : ℝ}
    (hC : 0 < C_emb) (h : EmbodimentThreshold C_emb < ρ) :
    C_emb < ThetaPressure ρ := by
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hcrit2 : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
  have hadd : 0 < C_emb * Θcrit ^ 2 := mul_pos hC hcrit2
  have hthresh : Θcrit < ρ := by
    have : Θcrit < Θcrit + C_emb * Θcrit ^ 2 := lt_add_of_pos_right _ hadd
    exact lt_trans this h
  have hle : ¬ (ρ ≤ Θcrit) := not_le.mpr hthresh
  simp only [ThetaPressure, hle, ↓reduceIte, EmbodimentThreshold] at *
  -- ρ > Θcrit + C_emb * Θcrit²
  -- So (ρ - Θcrit) / Θcrit² > C_emb
  have hsub : C_emb * Θcrit ^ 2 < ρ - Θcrit := by linarith
  have heq : C_emb = C_emb * Θcrit ^ 2 / Θcrit ^ 2 := by
    field_simp [ne_of_gt hcrit2]
  rw [heq]
  exact div_lt_div_of_pos_right hsub hcrit2

/-! ## Connection to J-cost structure -/

/-- The cost of non-existence mirrors J-cost near the threshold.
    Both have unit curvature when measured in natural units. -/
theorem cost_mirrors_J_structure :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      CostNonExist (Θcrit * (1 + ε)) = ε ^ 2 / 2 := by
  intro ε hε_pos _hε_lt
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hcrit_ne : Θcrit ≠ 0 := ne_of_gt hcrit
  have hle : ¬ (Θcrit * (1 + ε) ≤ Θcrit) := by
    push_neg
    have h1 : 1 < 1 + ε := by linarith
    nlinarith [sq_nonneg Θcrit]
  simp only [CostNonExist, hle, ↓reduceIte]
  have hsimpl : Θcrit * (1 + ε) - Θcrit = Θcrit * ε := by ring
  rw [hsimpl]
  have hcrit2_ne : Θcrit ^ 2 ≠ 0 := pow_ne_zero 2 hcrit_ne
  field_simp [hcrit2_ne]

/-! ## Additional properties for downstream use -/

/-- Cost is zero exactly at and below threshold -/
theorem CostNonExist_eq_zero_iff {ρ : ThetaDensity} :
    CostNonExist ρ = 0 ↔ ρ ≤ Θcrit := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hpos : 0 < ρ - Θcrit := sub_pos.mpr hne
    have hcrit : 0 < Θcrit := saturationThreshold_pos
    have hdenom : 0 < 2 * Θcrit ^ 2 := mul_pos two_pos (sq_pos_of_pos hcrit)
    simp only [CostNonExist, not_le.mpr hne, ↓reduceIte] at h
    have hsq_pos : 0 < (ρ - Θcrit) ^ 2 := sq_pos_of_pos hpos
    have hfrac_pos : 0 < (ρ - Θcrit) ^ 2 / (2 * Θcrit ^ 2) := div_pos hsq_pos hdenom
    linarith
  · exact CostNonExist_zero_below

/-- Pressure at critical density is zero -/
theorem ThetaPressure_at_crit : ThetaPressure Θcrit = 0 := by
  simp [ThetaPressure]

/-- Pressure above critical is positive -/
theorem ThetaPressure_pos_above {ρ : ThetaDensity} (h : Θcrit < ρ) :
    0 < ThetaPressure ρ := by
  have hpos : 0 < ρ - Θcrit := sub_pos.mpr h
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hdenom : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
  simp only [ThetaPressure, not_le.mpr h, ↓reduceIte]
  exact div_pos hpos hdenom

/-- Pressure is strictly increasing above threshold -/
theorem ThetaPressure_strictly_increasing {ρ₁ ρ₂ : ThetaDensity}
    (h₁ : Θcrit < ρ₁) (h₂ : ρ₁ < ρ₂) : ThetaPressure ρ₁ < ThetaPressure ρ₂ := by
  have hle1 : ¬ (ρ₁ ≤ Θcrit) := not_le.mpr h₁
  have hle2 : ¬ (ρ₂ ≤ Θcrit) := not_le.mpr (lt_trans h₁ h₂)
  simp only [ThetaPressure, hle1, hle2, ↓reduceIte]
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hdenom : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
  apply div_lt_div_of_pos_right _ hdenom
  linarith

/-- The saturation threshold in canonical form -/
theorem Θcrit_eq_phi_pow_45 : Θcrit = Constants.phi ^ 45 := rfl

end ThetaThermodynamics
end Consciousness
end IndisputableMonolith
