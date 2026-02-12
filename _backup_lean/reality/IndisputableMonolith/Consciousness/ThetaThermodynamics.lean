import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.Calibration
import IndisputableMonolith.Consciousness.PhaseSaturation

/-!
# Θ Thermodynamics — Parameter-Free *Given* Θcrit

This module upgrades the "finite capacity + saturation threshold" story into
a full thermodynamics with an equation of state, where **κ and γ are derived** once a
critical density `Θcrit` is specified.

## The Problem

We have:
- Θ-density ρ (patterns per resolution volume)
- Θ_crit (critical density; imported from `PhaseSaturation.SaturationThreshold`, currently `φ^45`)
- A "cost of non-existence" that was sketched as C(ρ) = κ(ρ−Θ_crit)^γ for ρ > Θ_crit

The question: **where do κ and γ come from?**

If RS is parameter-free, κ and γ cannot be arbitrary. They must derive from the
same uniqueness principles that fixed J and φ.

Note: Any claim that `Θcrit = φ^45` is a *capacity* (rather than a convenient scale choice)
depends on additional hypotheses about Light‑Field structure; see
`IndisputableMonolith.Consciousness.LightFieldCapacityGap45` and
`IndisputableMonolith.Consciousness.PhaseSaturationCapacityBridge` for a **conditional**
bridge.

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

/-! ### Θ-Density: Definition and Operationalization Status -/

/-- Θ-DENSITY: CONCEPTUAL DEFINITION AND OPERATIONAL STATUS

    ## Conceptual Definition

    Θ-density (ρ) represents the "density of recognition patterns" in a region
    of the Light-Memory field. It is measured in units of [patterns / (resolution volume)],
    where the resolution volume is set by the recognition length scale λ_rec.

    Conceptually: ρ = (number of Z-invariant patterns in region) / (volume in λ_rec³ units)

    ## Current Status: NON-OPERATIONAL (THEORETICAL CONSTRUCT)

    As of the current formalization, Θ-density is a **theoretical construct** with
    NO direct measurement protocol. This is explicitly acknowledged.

    The type `ThetaDensity := ℝ` is a placeholder that:
    1. Allows mathematical derivation of thermodynamic properties
    2. Enables cost/pressure calculations
    3. Does NOT claim we can currently measure ρ directly

    ## Why Operationalization Is Difficult

    Measuring Θ-density would require:
    1. Counting Z-invariant patterns (requires pattern detection technology)
    2. Defining a "resolution volume" (depends on observational scale)
    3. Distinguishing patterns from noise (requires coherence criterion)

    None of these are currently feasible with existing technology.

    ## Potential Future Proxies (SPECULATIVE)

    If RS predictions are validated, future operationalizations might include:
    1. **EEG coherence density**: measure phase-locking across neural regions
    2. **Reincarnation case density**: statistical rate of validated cases per population
    3. **Light-field perturbations**: if Θ-field affects matter, measure via interferometry

    All of these are speculative and would require extensive validation.

    ## Consequences of Non-Operationality

    The non-operational status means:
    - We cannot directly test thermodynamic predictions yet
    - Predictions about saturation, pressure, embodiment threshold remain theoretical
    - The model's validity rests on downstream predictions that ARE testable
      (e.g., reincarnation case features, NDE reports, consciousness threshold)

    ## Explicit Acknowledgment

    **This is a modeling convenience, NOT an empirical claim about measurability.**
    The mathematics is rigorous; the physical interpretation awaits measurement bridges.
-/
abbrev ThetaDensity := ℝ

/-! ### Operationalization Hypotheses -/

/-- **HYPOTHESIS H_DensityProxy_EEG**: EEG coherence as Θ-density proxy.

    **Speculative Claim**: Θ-density in a brain region correlates with
    the cross-electrode phase-locking value (PLV) in that region.

    **Rationale**: If conscious boundaries share global phase Θ,
    then higher boundary density → more phase-coherent neural activity.

    **Status**: SPECULATIVE HYPOTHESIS (not yet testable)
    **Prerequisites**: Need to establish consciousness/EEG mapping first.
    **Falsification**: No correlation between PLV and hypothesized conscious content. -/
def H_DensityProxy_EEG : Prop :=
  ∃ (f : ℝ → ℝ), -- Mapping from PLV (0 to 1) to Θ-density
    (∀ plv, 0 ≤ plv → plv ≤ 1 → 0 ≤ f plv) ∧  -- Non-negative density
    (∀ plv₁ plv₂, plv₁ < plv₂ → f plv₁ < f plv₂)  -- Monotonic

/-- **HYPOTHESIS H_DensityProxy_Population**: Population-based density estimate.

    **Speculative Claim**: Θ-density in the Light-Memory field can be estimated
    from the statistical rate of verified reincarnation cases.

    **Rationale**: Higher density → more pressure → more re-embodiment attempts
    → more observable cases (if detection is roughly uniform).

    **Status**: SPECULATIVE HYPOTHESIS (indirect)
    **Prerequisites**: Validated reincarnation case database.
    **Falsification**: Case rate doesn't correlate with predicted pressure model. -/
def H_DensityProxy_Population : Prop :=
  ∃ (g : ℝ → ℝ), -- Mapping from case rate (cases/million/year) to density
    (∀ rate, 0 ≤ rate → 0 ≤ g rate)  -- Non-negative

/-!
### Explicit Conclusion: Θ-density is currently non-operational

Direct measurement of Θ-density is not currently possible. Any use of Θ-density
in predictions must be mediated through indirect proxies or derived quantities.
Θ-density enters the theory as a theoretical construct constrained by
thermodynamic consistency and downstream empirical fits.
-/

/-- Status flag for Θ-density operationalization -/
def theta_density_operational_status : String :=
  "NON-OPERATIONAL: Θ-density is a theoretical construct without " ++
  "direct measurement protocol. Use with explicit proxy hypotheses."

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

/-- Cost is strictly positive above the threshold. -/
theorem CostNonExist_pos_above {ρ : ThetaDensity} (h : Θcrit < ρ) :
    0 < CostNonExist ρ := by
  have hle : ¬ (ρ ≤ Θcrit) := not_le.mpr h
  have hpos : 0 < ρ - Θcrit := sub_pos.mpr h
  have hsq_pos : 0 < (ρ - Θcrit) ^ 2 := sq_pos_of_pos hpos
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hdenom : 0 < 2 * Θcrit ^ 2 := mul_pos two_pos (sq_pos_of_pos hcrit)
  simp [CostNonExist, hle, div_pos hsq_pos hdenom]

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

/-! ## Monotonicity / convexity-style consequences -/

/-- `CostNonExist` is monotone (nondecreasing) in density. -/
theorem CostNonExist_mono {ρ₁ ρ₂ : ThetaDensity} (h : ρ₁ ≤ ρ₂) :
    CostNonExist ρ₁ ≤ CostNonExist ρ₂ := by
  by_cases h1 : ρ₁ ≤ Θcrit
  · -- then CostNonExist ρ₁ = 0 and RHS is nonnegative
    have : CostNonExist ρ₁ = 0 := CostNonExist_zero_below h1
    rw [this]
    exact CostNonExist_nonneg ρ₂
  · -- above-threshold branch for ρ₁; split on whether ρ₂ is also above
    push_neg at h1
    have hρ₁ : Θcrit < ρ₁ := h1
    by_cases h2 : ρ₂ ≤ Θcrit
    · -- impossible: ρ₁ > Θcrit but ρ₂ ≤ Θcrit with ρ₁ ≤ ρ₂
      exfalso
      have : ρ₁ ≤ Θcrit := le_trans h h2
      exact not_le.mpr hρ₁ this
    · push_neg at h2
      have hρ₂ : Θcrit < ρ₂ := h2
      -- strict increasing plus ≤ gives monotone
      by_cases heq : ρ₁ = ρ₂
      · simpa [heq]
      · have hlt : ρ₁ < ρ₂ := lt_of_le_of_ne h heq
        exact le_of_lt (CostNonExist_strictly_increasing hρ₁ hlt)


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

/-- `ThetaPressure` is monotone (nondecreasing) in density. -/
theorem ThetaPressure_mono {ρ₁ ρ₂ : ThetaDensity} (h : ρ₁ ≤ ρ₂) :
    ThetaPressure ρ₁ ≤ ThetaPressure ρ₂ := by
  by_cases h1 : ρ₁ ≤ Θcrit
  · -- LHS = 0; RHS is nonnegative
    have hL : ThetaPressure ρ₁ = 0 := by simp [ThetaPressure, h1]
    rw [hL]
    exact ThetaPressure_nonneg ρ₂
  · push_neg at h1
    have hρ₁ : Θcrit < ρ₁ := h1
    by_cases h2 : ρ₂ ≤ Θcrit
    · -- contradiction with ρ₁ ≤ ρ₂
      exfalso
      have : ρ₁ ≤ Θcrit := le_trans h h2
      exact not_le.mpr hρ₁ this
    · push_neg at h2
      have hle1 : ¬ (ρ₁ ≤ Θcrit) := not_le.mpr hρ₁
      have hle2 : ¬ (ρ₂ ≤ Θcrit) := not_le.mpr h2
      simp only [ThetaPressure, hle1, hle2, ↓reduceIte]
      have hcrit : 0 < Θcrit := saturationThreshold_pos
      have hdenom : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
      exact div_le_div_of_nonneg_right (sub_le_sub_right h _) (le_of_lt hdenom)

/-! ## Embodiment threshold: when binding becomes favored -/

/-- The density at which embodiment becomes favored by **cost comparison**.

Above this density, the added cost of remaining in Light Memory (`CostNonExist`) exceeds the
embodiment cost `C_emb`.

This matches the prose criterion: `Cost(Non-Existence) > Cost(Existence)`.

Note: we intentionally compare **cost to cost**, not pressure to cost. -/
noncomputable def EmbodimentThreshold (C_emb : ℝ) : ThetaDensity :=
  Θcrit + Θcrit * Real.sqrt (2 * C_emb)

/-- At the embodiment threshold, the non-existence cost equals the embodiment cost. -/
theorem CostNonExist_at_EmbodimentThreshold {C_emb : ℝ} (hC : 0 ≤ C_emb) :
    CostNonExist (EmbodimentThreshold C_emb) = C_emb := by
  by_cases h0 : C_emb = 0
  · subst h0
    -- EmbodimentThreshold 0 = Θcrit and CostNonExist Θcrit = 0
    simp [EmbodimentThreshold, CostNonExist]
  · have hCpos : 0 < C_emb := lt_of_le_of_ne hC (Ne.symm h0)
    have hcrit : 0 < Θcrit := saturationThreshold_pos
    have hsqrt_pos : 0 < Real.sqrt (2 * C_emb) := by
      have : 0 < 2 * C_emb := by nlinarith [hCpos]
      exact Real.sqrt_pos.mpr this
    have hρcrit : Θcrit < EmbodimentThreshold C_emb := by
      unfold EmbodimentThreshold
      have : 0 < Θcrit * Real.sqrt (2 * C_emb) := mul_pos hcrit hsqrt_pos
      linarith
    have hle : ¬ (EmbodimentThreshold C_emb ≤ Θcrit) := not_le.mpr hρcrit
    -- Expand the quadratic and simplify.
    simp only [CostNonExist, hle, ↓reduceIte]
    have hsqrt_sq : (Real.sqrt (2 * C_emb)) ^ 2 = 2 * C_emb := by
      simpa using Real.sq_sqrt (by nlinarith [hC] : 0 ≤ (2 * C_emb))
    have hΘcrit2_ne : Θcrit ^ 2 ≠ 0 := by exact pow_ne_zero 2 (ne_of_gt hcrit)
    -- (ρ-Θcrit) = Θcrit*sqrt(2*C_emb)
    have hsub : EmbodimentThreshold C_emb - Θcrit = Θcrit * Real.sqrt (2 * C_emb) := by
      unfold EmbodimentThreshold
      ring
    -- Compute
    rw [hsub]
    -- (Θcrit*sqrt)^2 = Θcrit^2 * (sqrt^2)
    calc
      (Θcrit * Real.sqrt (2 * C_emb)) ^ 2 / (2 * Θcrit ^ 2)
          = (Θcrit ^ 2 * (Real.sqrt (2 * C_emb)) ^ 2) / (2 * Θcrit ^ 2) := by
              simpa [mul_pow]
      _ = (Θcrit ^ 2 * (2 * C_emb)) / (2 * Θcrit ^ 2) := by
              rw [hsqrt_sq]
      _ = C_emb := by
              field_simp [hΘcrit2_ne]

theorem embodiment_favored_above_threshold {ρ : ThetaDensity} {C_emb : ℝ}
    (hC : 0 ≤ C_emb) (h : EmbodimentThreshold C_emb < ρ) :
    C_emb < CostNonExist ρ := by
  have hcrit : 0 < Θcrit := saturationThreshold_pos

  -- Handle the edge case C_emb = 0 separately (then the claim is `0 < CostNonExist ρ`).
  by_cases hC0 : C_emb = 0
  · subst hC0
    have hρcrit : Θcrit < ρ := by
      -- EmbodimentThreshold 0 = Θcrit since sqrt(0)=0
      simpa [EmbodimentThreshold] using h
    have hle : ¬ (ρ ≤ Θcrit) := not_le.mpr hρcrit
    have hpos : 0 < (ρ - Θcrit) ^ 2 := by
      have : 0 < ρ - Θcrit := sub_pos.mpr hρcrit
      exact sq_pos_of_pos this
    have hdenom : 0 < 2 * Θcrit ^ 2 := by
      have : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
      exact mul_pos two_pos this
    have : 0 < CostNonExist ρ := by
      -- CostNonExist ρ = (ρ-Θcrit)^2/(2*Θcrit^2) above threshold
      simp [CostNonExist, hle, div_pos hpos hdenom]
    simpa using this
  · have hCpos : 0 < C_emb := lt_of_le_of_ne hC (Ne.symm hC0)

    -- From ρ > Θcrit + Θcrit*sqrt(2*C_emb) we get Θcrit*sqrt(2*C_emb) < ρ - Θcrit.
    have hδ : Θcrit * Real.sqrt (2 * C_emb) < ρ - Θcrit := by
      unfold EmbodimentThreshold at h
      linarith

    -- Square the inequality (both sides are > 0 in this branch).
    have hsq :
        (Θcrit * Real.sqrt (2 * C_emb)) ^ 2 < (ρ - Θcrit) ^ 2 := by
      set a : ℝ := Θcrit * Real.sqrt (2 * C_emb)
      set b : ℝ := ρ - Θcrit
      have hsqrt_pos : 0 < Real.sqrt (2 * C_emb) := by
        have : 0 < 2 * C_emb := by nlinarith [hCpos]
        exact Real.sqrt_pos.mpr this
      have ha_pos : 0 < a := by
        -- Θcrit > 0 and sqrt(2*C_emb) > 0
        simpa [a] using (mul_pos hcrit hsqrt_pos)
      have hab : a < b := by
        simpa [a, b] using hδ
      have hb_pos : 0 < b := lt_trans ha_pos hab
      have h1 : a * a < a * b := mul_lt_mul_of_pos_left hab ha_pos
      have h2 : a * b < b * b := mul_lt_mul_of_pos_right hab hb_pos
      have hmul : a * a < b * b := lt_trans h1 h2
      have hsq' : a ^ 2 < b ^ 2 := by simpa [pow_two] using hmul
      -- Unfold a and b without rewriting `sqrt (2*C_emb)` into `sqrt2 * sqrtC_emb`.
      dsimp [a, b] at hsq'
      exact hsq'

    have hρcrit : Θcrit < ρ := by
      -- Left side of hδ is > 0 in this branch, so ρ - Θcrit > 0.
      have hsqrt_pos : 0 < Real.sqrt (2 * C_emb) := by
        have : 0 < 2 * C_emb := by nlinarith [hCpos]
        exact Real.sqrt_pos.mpr this
      have ha_pos : 0 < Θcrit * Real.sqrt (2 * C_emb) := mul_pos hcrit hsqrt_pos
      have hb_pos : 0 < ρ - Θcrit := lt_trans ha_pos hδ
      exact sub_pos.mp hb_pos
    have hle : ¬ (ρ ≤ Θcrit) := not_le.mpr hρcrit

    have hsqrt_sq : (Real.sqrt (2 * C_emb)) ^ 2 = 2 * C_emb := by
      -- sqrt(x)^2 = x for x ≥ 0
      simpa using Real.sq_sqrt (by nlinarith [hC] : 0 ≤ (2 * C_emb))

    have hleft_sq : (Θcrit * Real.sqrt (2 * C_emb)) ^ 2 = Θcrit ^ 2 * (2 * C_emb) := by
      calc
        (Θcrit * Real.sqrt (2 * C_emb)) ^ 2
            = Θcrit ^ 2 * (Real.sqrt (2 * C_emb)) ^ 2 := by
                simpa [mul_pow]
        _ = Θcrit ^ 2 * (2 * C_emb) := by
            rw [hsqrt_sq]

    have hsq'' : Θcrit ^ 2 * (2 * C_emb) < (ρ - Θcrit) ^ 2 := by
      -- Rewrite the left-hand side using `hleft_sq` and reuse the squared inequality `hsq`.
      calc
        Θcrit ^ 2 * (2 * C_emb) = (Θcrit * Real.sqrt (2 * C_emb)) ^ 2 := by
          exact hleft_sq.symm
        _ < (ρ - Θcrit) ^ 2 := hsq

    have hdenom_pos : 0 < 2 * Θcrit ^ 2 := by
      have : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
      exact mul_pos two_pos this

    have hdiv :
        (Θcrit ^ 2 * (2 * C_emb)) / (2 * Θcrit ^ 2) < (ρ - Θcrit) ^ 2 / (2 * Θcrit ^ 2) :=
      div_lt_div_of_pos_right hsq'' hdenom_pos

    have hΘcrit2_ne : Θcrit ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (ne_of_gt hcrit)
    have hleft_simp : (Θcrit ^ 2 * (2 * C_emb)) / (2 * Θcrit ^ 2) = C_emb := by
      field_simp [hΘcrit2_ne]

    have hCost : CostNonExist ρ = (ρ - Θcrit) ^ 2 / (2 * Θcrit ^ 2) := by
      simp [CostNonExist, hle]

    have : C_emb < (ρ - Θcrit) ^ 2 / (2 * Θcrit ^ 2) := by
      simpa [hleft_simp] using hdiv
    simpa [hCost] using this

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

/-- `CostNonExist` is continuous (it is a quadratic glued to 0 at the threshold). -/
theorem CostNonExist_continuous : Continuous CostNonExist := by
  -- Use `Continuous.if` with the frontier of `Iic Θcrit` being `{Θcrit}`.
  have hf : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hg : Continuous (fun ρ : ℝ => (ρ - Θcrit) ^ 2 / (2 * Θcrit ^ 2)) := by
    have hsub : Continuous (fun ρ : ℝ => ρ - Θcrit) :=
      Continuous.sub continuous_id continuous_const
    have hsq : Continuous (fun ρ : ℝ => (ρ - Θcrit) ^ 2) :=
      Continuous.pow hsub 2
    exact Continuous.div_const hsq (2 * Θcrit ^ 2)
  have hp :
      ∀ a ∈ frontier {x : ℝ | x ≤ Θcrit},
        (0 : ℝ) = (a - Θcrit) ^ 2 / (2 * Θcrit ^ 2) := by
    intro a ha
    have ha' : a ∈ frontier (Set.Iic Θcrit) := by
      simpa [Set.Iic] using ha
    have : a ∈ ({Θcrit} : Set ℝ) := by
      simpa [frontier_Iic] using ha'
    have hEq : a = Θcrit := by simpa using this
    subst hEq
    simp
  -- `CostNonExist` is `if ρ ≤ Θcrit then 0 else ...`.
  -- Need to convert because Continuous.if normalizes ^ 2 to * form
  have heq : CostNonExist = fun ρ => if ρ ≤ Θcrit then 0 else (ρ - Θcrit) ^ 2 / (2 * Θcrit ^ 2) := rfl
  rw [heq]
  exact Continuous.if hp hf hg

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

/-- `ThetaPressure` is continuous (linear glued to 0 at the threshold). -/
theorem ThetaPressure_continuous : Continuous ThetaPressure := by
  have hf : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hg : Continuous (fun ρ : ℝ => (ρ - Θcrit) / (Θcrit ^ 2)) := by
    have hsub : Continuous (fun ρ : ℝ => ρ - Θcrit) :=
      Continuous.sub continuous_id continuous_const
    exact Continuous.div_const hsub (Θcrit ^ 2)
  have hp :
      ∀ a ∈ frontier {x : ℝ | x ≤ Θcrit},
        (0 : ℝ) = (a - Θcrit) / (Θcrit ^ 2) := by
    intro a ha
    have ha' : a ∈ frontier (Set.Iic Θcrit) := by
      simpa [Set.Iic] using ha
    have : a ∈ ({Θcrit} : Set ℝ) := by
      simpa [frontier_Iic] using ha'
    have hEq : a = Θcrit := by simpa using this
    subst hEq
    simp
  simpa [ThetaPressure] using (Continuous.if hp hf hg)

/-! ## Convexity (T1.1) -/

/-- The above-threshold cost function ρ ↦ (ρ - Θcrit)² / (2·Θcrit²) is convex.

    This is a translated and scaled quadratic, hence convex on ℝ.
    The quadratic x² is convex, and positive-scaling + translation preserve convexity. -/
theorem CostNonExist_aboveThreshold_convexOn :
    ConvexOn ℝ (Set.Ici Θcrit) (fun ρ => (ρ - Θcrit) ^ 2 / (2 * Θcrit ^ 2)) := by
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hdenom_pos : 0 < 2 * Θcrit ^ 2 := mul_pos two_pos (sq_pos_of_pos hcrit)
  have hdenom_nonneg : 0 ≤ 2 * Θcrit ^ 2 := le_of_lt hdenom_pos
  -- Strategy: show convexity by direct computation on the convex set
  refine ⟨convex_Ici Θcrit, ?_⟩
  intros x hx y hy a b ha hb hab
  -- Need: f(a*x + b*y) ≤ a*f(x) + b*f(y)
  -- where f(ρ) = (ρ - Θcrit)² / (2*Θcrit²)
  -- Let u = x - Θcrit, v = y - Θcrit, then u,v ≥ 0 and
  -- f(a*x + b*y) = (a*u + b*v)² / (2*Θcrit²)
  set u := x - Θcrit with hu_def
  set v := y - Θcrit with hv_def
  have hu_nonneg : 0 ≤ u := sub_nonneg.mpr hx
  have hv_nonneg : 0 ≤ v := sub_nonneg.mpr hy
  -- The key inequality is (a*u + b*v)² ≤ a*u² + b*v² when a+b=1, a,b≥0
  have hconv_sq : (a * u + b * v) ^ 2 ≤ a * u ^ 2 + b * v ^ 2 := by
    -- Use convexity of x² on [0, ∞), noting u, v ≥ 0
    have hsq_conv : ConvexOn ℝ (Set.Ici 0) (fun z : ℝ => z ^ 2) := convexOn_pow 2
    have hmem_u : u ∈ Set.Ici (0 : ℝ) := hu_nonneg
    have hmem_v : v ∈ Set.Ici (0 : ℝ) := hv_nonneg
    exact hsq_conv.2 hmem_u hmem_v ha hb hab
  -- Show the inequality
  simp only [smul_eq_mul]
  have hlhs : (a * x + b * y - Θcrit) = a * u + b * v := by
    simp only [hu_def, hv_def]
    -- a*x + b*y - Θcrit = a*(x - Θcrit) + b*(y - Θcrit)
    --                   = a*x - a*Θcrit + b*y - b*Θcrit
    --                   = a*x + b*y - (a + b)*Θcrit
    --                   = a*x + b*y - Θcrit     [since a + b = 1]
    have h1 : a * x + b * y - Θcrit = a * x + b * y - (a + b) * Θcrit := by
      rw [hab]; ring
    have h2 : a * x + b * y - (a + b) * Θcrit = a * (x - Θcrit) + b * (y - Θcrit) := by ring
    linarith [h1, h2]
  have hrhs : a * ((x - Θcrit) ^ 2 / (2 * Θcrit ^ 2)) + b * ((y - Θcrit) ^ 2 / (2 * Θcrit ^ 2))
            = (a * u ^ 2 + b * v ^ 2) / (2 * Θcrit ^ 2) := by
    simp only [hu_def, hv_def]
    field_simp [ne_of_gt hdenom_pos]
  rw [hlhs, hrhs]
  exact div_le_div_of_nonneg_right hconv_sq hdenom_nonneg

/-- `ThetaPressure` is linear (hence convex) above threshold.

    The function ρ ↦ (ρ - Θcrit) / Θcrit² is affine, hence convex. -/
theorem ThetaPressure_aboveThreshold_convexOn :
    ConvexOn ℝ (Set.Ici Θcrit) (fun ρ => (ρ - Θcrit) / Θcrit ^ 2) := by
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hdenom_pos : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
  -- Affine functions are convex: f(ax + by) = a·f(x) + b·f(y)
  refine ⟨convex_Ici Θcrit, ?_⟩
  intros x _hx y _hy a b _ha _hb hab
  -- The function (ρ - Θcrit) / Θcrit² is affine (linear + constant)
  simp only [smul_eq_mul]
  -- For affine functions, the inequality is actually an equality
  have heq : (a * x + b * y - Θcrit) / Θcrit ^ 2
           = a * ((x - Θcrit) / Θcrit ^ 2) + b * ((y - Θcrit) / Θcrit ^ 2) := by
    have h1 : a * x + b * y - Θcrit = a * x + b * y - (a + b) * Θcrit := by rw [hab]; ring
    rw [h1]
    field_simp [ne_of_gt hdenom_pos]
    ring
  linarith [heq.ge]

/-! ## Differentiability (T1.1) -/

/-- The above-threshold cost has derivative equal to `ThetaPressure`.

    d/dρ [(ρ - Θcrit)² / (2·Θcrit²)] = (ρ - Θcrit) / Θcrit²  -/
theorem CostNonExist_hasDerivAt_above {ρ : ℝ} (h : Θcrit < ρ) :
    HasDerivAt (fun x => (x - Θcrit) ^ 2 / (2 * Θcrit ^ 2))
               ((ρ - Θcrit) / Θcrit ^ 2) ρ := by
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hdenom : 0 < 2 * Θcrit ^ 2 := mul_pos two_pos (sq_pos_of_pos hcrit)
  have hdenom_ne : 2 * Θcrit ^ 2 ≠ 0 := ne_of_gt hdenom
  -- d/dx [(x-c)² / k] = 2(x-c) / k
  have h1 : HasDerivAt (fun x => x - Θcrit) 1 ρ :=
    (hasDerivAt_id ρ).sub_const Θcrit
  -- Power rule: d/dx [u²] = 2u·u'
  have h2 : HasDerivAt (fun x => (x - Θcrit) ^ 2) (2 * (ρ - Θcrit)) ρ := by
    convert h1.pow 2 using 1
    ring
  have h3 : HasDerivAt (fun x => (x - Θcrit) ^ 2 / (2 * Θcrit ^ 2))
                       ((2 * (ρ - Θcrit)) / (2 * Θcrit ^ 2)) ρ :=
    h2.div_const (2 * Θcrit ^ 2)
  -- Simplify: 2*(ρ-Θcrit)/(2*Θcrit²) = (ρ-Θcrit)/Θcrit²
  convert h3 using 1
  have hΘcrit_ne : Θcrit ≠ 0 := ne_of_gt hcrit
  field_simp [hdenom_ne, hΘcrit_ne]

/-- `ThetaPressure` has constant derivative 1/Θcrit² above threshold. -/
theorem ThetaPressure_hasDerivAt_above {ρ : ℝ} (_h : Θcrit < ρ) :
    HasDerivAt (fun x => (x - Θcrit) / Θcrit ^ 2)
               (1 / Θcrit ^ 2) ρ := by
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hdenom : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
  have h1 : HasDerivAt (fun x => x - Θcrit) 1 ρ :=
    (hasDerivAt_id ρ).sub_const Θcrit
  exact h1.div_const (Θcrit ^ 2)

/-- `CostNonExist` is differentiable on (Θcrit, ∞).

    On this open interval, `CostNonExist` equals the smooth function
    `(ρ - Θcrit)² / (2·Θcrit²)`, hence is differentiable. -/
theorem CostNonExist_differentiableOn_above :
    DifferentiableOn ℝ CostNonExist (Set.Ioi Θcrit) := by
  intro ρ hρ
  have hle : ¬ (ρ ≤ Θcrit) := not_le.mpr hρ
  -- The underlying function is smooth
  have hdiff : DifferentiableAt ℝ (fun x => (x - Θcrit) ^ 2 / (2 * Θcrit ^ 2)) ρ :=
    (CostNonExist_hasDerivAt_above hρ).differentiableAt
  -- CostNonExist agrees with the smooth function on the set
  apply DifferentiableWithinAt.congr hdiff.differentiableWithinAt
  · intros x hx
    have hx_gt : Θcrit < x := hx
    simp only [CostNonExist, not_le.mpr hx_gt, ↓reduceIte]
  · simp only [CostNonExist, hle, ↓reduceIte]

/-- `ThetaPressure` is differentiable on (Θcrit, ∞).

    On this open interval, `ThetaPressure` equals the smooth function
    `(ρ - Θcrit) / Θcrit²`, hence is differentiable. -/
theorem ThetaPressure_differentiableOn_above :
    DifferentiableOn ℝ ThetaPressure (Set.Ioi Θcrit) := by
  intro ρ hρ
  have hle : ¬ (ρ ≤ Θcrit) := not_le.mpr hρ
  -- The underlying function is smooth
  have hdiff : DifferentiableAt ℝ (fun x => (x - Θcrit) / Θcrit ^ 2) ρ :=
    (ThetaPressure_hasDerivAt_above hρ).differentiableAt
  -- ThetaPressure agrees with the smooth function on the set
  apply DifferentiableWithinAt.congr hdiff.differentiableWithinAt
  · intros x hx
    have hx_gt : Θcrit < x := hx
    simp only [ThetaPressure, not_le.mpr hx_gt, ↓reduceIte]
  · simp only [ThetaPressure, hle, ↓reduceIte]

/-- The Θ-thermodynamics non-existence cost coincides with the PhaseSaturation cost law. -/
theorem CostNonExist_eq_PhaseSaturation_NonExistenceCost (ρ : ThetaDensity) :
    CostNonExist ρ = PhaseSaturation.NonExistenceCost ρ := by
  -- Both are the same piecewise quadratic, and `Θcrit` is an abbrev for `SaturationThreshold`.
  simp [CostNonExist, PhaseSaturation.NonExistenceCost, Θcrit]

/-- The saturation threshold in canonical form -/
theorem Θcrit_eq_phi_pow_45 : Θcrit = Constants.phi ^ 45 := rfl

end ThetaThermodynamics
end Consciousness
end IndisputableMonolith
