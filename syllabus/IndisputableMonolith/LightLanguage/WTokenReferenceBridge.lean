import Mathlib
import IndisputableMonolith.Foundation.WTokenReference
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# WToken Reference Bridge: Connecting Algebra to Aboutness

This module bridges the **WToken framework** with the **Algebra of Aboutness**
(reference, cost, compression).

## The Key Insight

WTokens are semantic atoms that can be understood through reference theory:
- Each WToken has an intrinsic cost J(φ^level)
- Reference between WTokens is J(ratio₁ / ratio₂)
- Level-0 WTokens have J = 0 (universal compressors)

## Main Results

1. **Amplitude-to-Cost**: |z| → J(|z|)
2. **WToken composition bounds**: d'Alembert inequality
3. **Neutral structures have balanced reference**

-/

namespace IndisputableMonolith
namespace LightLanguage
namespace WTokenReferenceBridge

open Foundation.Reference
open Foundation.WTokenReference
open Foundation.ReferenceWToken
open Cost
open Constants

/-! ## Part 1: Amplitude to Cost Mapping -/

/-- Map a real amplitude to its J-cost.

    The cost is J(a) for amplitude a > 0.
    For a = 1, cost is 0 (balanced).
-/
noncomputable def amplitudeToCost (a : ℝ) (ha : 0 < a) : ℝ :=
  Jcost a

/-- Unit amplitude has zero cost. -/
theorem unit_amplitude_zero_cost : amplitudeToCost 1 (by norm_num) = 0 :=
  Jcost_unit0

/-- Cost is symmetric under reciprocation. -/
theorem amplitude_cost_symmetric (a : ℝ) (ha : 0 < a) :
    amplitudeToCost a ha = amplitudeToCost a⁻¹ (inv_pos.mpr ha) :=
  Jcost_symm ha

/-! ## Part 2: φ-Level Costs -/

/-- The cost at each φ-level.

    | Level | Ratio | Approx Cost |
    |-------|-------|-------------|
    | 0     | 1     | 0           |
    | 1     | φ     | 0.118       |
    | 2     | φ²    | 0.382       |
    | 3     | φ³    | 0.854       |
-/
noncomputable def phiLevelCost (level : ℕ) : ℝ :=
  Jcost (phi ^ level)

/-- Level 0 has zero cost. -/
theorem phiLevelCost_zero : phiLevelCost 0 = 0 := by
  simp [phiLevelCost, Jcost_unit0]

/-- `Jcost` is strictly increasing on `(1, ∞)`.

This is an algebraic (non-calculus) proof: for `1 < a < b`,
\[
(b + b^{-1}) - (a + a^{-1}) = (b-a)\left(1 - \frac{1}{ab}\right) > 0,
\]
since `b-a > 0` and `ab > 1`.
-/
lemma Jcost_lt_of_one_lt_of_lt {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    Jcost a < Jcost b := by
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hb1 : 1 < b := lt_trans ha hab
  have hb0 : 0 < b := lt_trans (by norm_num) hb1
  have hba : 0 < b - a := sub_pos.mpr hab
  have hab_gt : 1 < a * b := by
    have hb_lt : b < a * b := by
      -- b = 1*b < a*b since 1<a and b>0
      simpa [one_mul] using (mul_lt_mul_of_pos_right ha hb0)
    exact lt_trans hb1 hb_lt
  have hinv_lt : 1 / (a * b) < 1 := by
    -- from 1 < a*b, invert (positive) to get 1/(a*b) < 1/1
    have h :=
      one_div_lt_one_div_of_lt (show (0 : ℝ) < (1 : ℝ) by norm_num) hab_gt
    simpa using h
  have hfactor : 0 < 1 - 1 / (a * b) := sub_pos.mpr hinv_lt
  have hprod : 0 < (b - a) * (1 - 1 / (a * b)) := mul_pos hba hfactor
  have hdiff : (b + b⁻¹) - (a + a⁻¹) = (b - a) * (1 - 1 / (a * b)) := by
    have ha_ne : a ≠ 0 := ne_of_gt ha0
    have hb_ne : b ≠ 0 := ne_of_gt hb0
    have hab_ne : a * b ≠ 0 := mul_ne_zero ha_ne hb_ne
    field_simp [ha_ne, hb_ne, hab_ne]
    ring
  have hsum : a + a⁻¹ < b + b⁻¹ := by
    have : 0 < (b + b⁻¹) - (a + a⁻¹) := by
      simpa [hdiff] using hprod
    linarith
  unfold Jcost
  linarith

/-- Costs strictly increase along the φ-level ladder.

This supports the interpretation that higher φ-levels encode richer (higher-cost) semantics.
-/
theorem phiLevelCost_mono {n m : ℕ} (hnm : n < m) :
    phiLevelCost n < phiLevelCost m := by
  unfold phiLevelCost
  cases n with
  | zero =>
    -- J(1)=0 < J(φ^m) for m>0
    have hm0 : m ≠ 0 := Nat.ne_zero_of_lt hnm
    have hm_pos : 0 < phi ^ m := pow_pos phi_pos _
    have hm_ne_one : phi ^ m ≠ 1 := by
      have hm_gt : 1 < phi ^ m := one_lt_pow₀ one_lt_phi hm0
      exact ne_of_gt hm_gt
    have : 0 < Jcost (phi ^ m) := Jcost_pos_of_ne_one (phi ^ m) hm_pos hm_ne_one
    simpa [pow_zero, Jcost_unit0] using this
  | succ n' =>
    have ha : 1 < phi ^ (Nat.succ n') := one_lt_pow₀ one_lt_phi (Nat.succ_ne_zero n')
    have hab : phi ^ (Nat.succ n') < phi ^ m := pow_lt_pow_right₀ one_lt_phi hnm
    exact Jcost_lt_of_one_lt_of_lt ha hab

/-! ## Part 3: Reference Cost Between Levels -/

/-- The reference cost between two φ-levels.

    R(level₁, level₂) = J(φ^level₁ / φ^level₂) = J(φ^(level₁ - level₂))
-/
noncomputable def levelReferenceCost (level₁ level₂ : ℕ) : ℝ :=
  Jcost (phi ^ level₁ / phi ^ level₂)

/-- Self-reference has zero cost. -/
theorem level_self_reference_zero (level : ℕ) :
    levelReferenceCost level level = 0 := by
  unfold levelReferenceCost
  rw [div_self (pow_ne_zero level (ne_of_gt phi_pos))]
  exact Jcost_unit0

/-- Reference cost is symmetric in levels (via J symmetry). -/
theorem level_reference_symmetric (level₁ level₂ : ℕ) :
    levelReferenceCost level₁ level₂ = levelReferenceCost level₂ level₁ := by
  unfold levelReferenceCost
  rw [Jcost_symm (div_pos (pow_pos phi_pos _) (pow_pos phi_pos _))]
  congr 1
  rw [inv_div]

/-! ## Part 4: The d'Alembert Composition Bound -/

/-- Reference cost satisfies the d'Alembert bound under composition.

    R(level₁, level₃) ≤ 2R(level₁, level₂) + 2R(level₂, level₃) + 2R₁₂·R₂₃
-/
theorem level_reference_dalembert (level₁ level₂ level₃ : ℕ) :
    levelReferenceCost level₁ level₃ ≤
    2 * levelReferenceCost level₁ level₂ + 2 * levelReferenceCost level₂ level₃ +
    2 * levelReferenceCost level₁ level₂ * levelReferenceCost level₂ level₃ := by
  unfold levelReferenceCost
  -- φ^l₁ / φ^l₃ = (φ^l₁ / φ^l₂) * (φ^l₂ / φ^l₃)
  have h_decomp : phi ^ level₁ / phi ^ level₃ =
                  (phi ^ level₁ / phi ^ level₂) * (phi ^ level₂ / phi ^ level₃) := by
    have h1 : phi ^ level₂ ≠ 0 := pow_ne_zero _ phi_ne_zero
    have h2 : phi ^ level₃ ≠ 0 := pow_ne_zero _ phi_ne_zero
    field_simp [h1, h2]
  rw [h_decomp]
  exact Jcost_submult (div_pos (pow_pos phi_pos _) (pow_pos phi_pos _))
                      (div_pos (pow_pos phi_pos _) (pow_pos phi_pos _))

/-! ## Part 5: WToken Selection by Cost -/

/-- Select the optimal φ-level for a given target ratio.

    Returns the level k ∈ {0,1,2,3} that minimizes J(target / φ^k).
-/
noncomputable def selectOptimalLevel (target : ℝ) (ht : 0 < target) : ℕ :=
  let log_target := Real.log target / Real.log phi
  if log_target < 0.5 then 0
  else if log_target < 1.5 then 1
  else if log_target < 2.5 then 2
  else 3

/-- For unit target, select level 0. -/
theorem selectOptimalLevel_one :
    selectOptimalLevel 1 (by norm_num) = 0 := by
  unfold selectOptimalLevel
  simp only [Real.log_one, zero_div]
  norm_num

/-- For target = φ, select level 1. -/
theorem selectOptimalLevel_phi :
    selectOptimalLevel phi phi_pos = 1 := by
  unfold selectOptimalLevel
  simp only [div_self (Real.log_ne_zero_of_pos_of_ne_one phi_pos (ne_of_gt one_lt_phi))]
  norm_num

/-! ## Part 6: Summary -/

/-- **BRIDGE SUMMARY**:

    1. Amplitude → J-cost (unit has zero cost)
    2. φ-level costs are defined via J(φ^k)
    3. Reference cost = J(ratio difference)
    4. d'Alembert bounds composition
    5. Optimal selection by log-rounding
-/
theorem wtoken_reference_bridge_summary :
    -- Unit amplitude is zero cost
    amplitudeToCost 1 (by norm_num) = 0 ∧
    -- Level 0 is zero cost
    phiLevelCost 0 = 0 ∧
    -- Self-reference is zero
    (∀ n, levelReferenceCost n n = 0) ∧
    -- Reference is symmetric
    (∀ n m, levelReferenceCost n m = levelReferenceCost m n) ∧
    -- Unit target selects level 0
    selectOptimalLevel 1 (by norm_num) = 0 :=
  ⟨unit_amplitude_zero_cost, phiLevelCost_zero, level_self_reference_zero,
   level_reference_symmetric, selectOptimalLevel_one⟩

#check wtoken_reference_bridge_summary

end WTokenReferenceBridge
end LightLanguage
end IndisputableMonolith
