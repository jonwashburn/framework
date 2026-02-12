import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Consciousness.LightMemory
import IndisputableMonolith.Consciousness.GlobalPhase
import IndisputableMonolith.Gap45.GroupView

/-!
# Phase Saturation: Why Rebirth Occurs

This module addresses the paradox: If the Light Memory state is zero-cost and stable,
**why does anything reincarnate?** Why doesn't the universe relax into a static Light Field?

## The Solution: Birth as Phase Transition

As Z-patterns accumulate in the massless Light Memory state, they increase local
**Phase Density (Θ-density)**. Eventually:

    Cost(Non-Existence) > Cost(Existence)

In this saturation model, re-embodiment becomes thermodynamically favored once the
cost of remaining in Light Memory exceeds an embodiment cost.

## Key Insight

The Light Field is NOT infinitely capacious. There's a saturation threshold (φ^45,
modeled as φ^45 and motivated by Gap-45 scaling) above which the saturation cost is nonzero.

This completes the Life-Death-Rebirth cycle:

    Life → Death → Light Memory → Saturation → Rebirth → Life

-/

namespace IndisputableMonolith
namespace Consciousness
namespace PhaseSaturation

open Constants
open Foundation

/-! ## Phase Density -/

/-- A region of the Light Field (abstract spatial domain) -/
structure Region where
  /-- Volume of the region (positive measure) -/
  volume : ℝ
  /-- Volume is positive -/
  volume_pos : 0 < volume

/-- **PHASE DENSITY**

    The density of Z-patterns in a region of the Light Field.
    When this exceeds the saturation threshold, re-embodiment is favored. -/
noncomputable def PhaseDensity (patterns : Finset LightMemoryState) (region : Region) : ℝ :=
  patterns.card / region.volume

/-- Phase density is nonnegative -/
theorem phaseDensity_nonneg (patterns : Finset LightMemoryState) (region : Region) :
    0 ≤ PhaseDensity patterns region := by
  unfold PhaseDensity
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · exact le_of_lt region.volume_pos

/-! ## Saturation Threshold -/

/-- **SATURATION THRESHOLD**

    The phase density above which re-embodiment becomes favored.
    Current model choice: `φ^45` (motivated by Gap‑45 scaling).

    Interpretation note (discovery posture):
    - Treating this as a **Light‑Field capacity** requires additional structure.
      See `IndisputableMonolith.Consciousness.LightFieldCapacityGap45` for a
      **conditional** identification of a derived capacity scale with `φ^45`,
      and `IndisputableMonolith.Consciousness.PhaseSaturationCapacityBridge` for the
      wiring lemma back to this definition. -/
noncomputable def SaturationThreshold : ℝ := phi ^ 45

/-- Saturation threshold is positive -/
theorem saturationThreshold_pos : 0 < SaturationThreshold := by
  unfold SaturationThreshold
  exact pow_pos phi_pos 45

/-- Helper: φ > 1.6 (used for power bounds) -/
lemma phi_gt_16 : phi > 1.6 := by
  have hsqrt5 : Real.sqrt 5 > 2.2 := by
    have h4_84 : (4.84 : ℝ) < 5 := by norm_num
    have hsq : Real.sqrt 4.84 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) h4_84
    have heq : Real.sqrt 4.84 = 2.2 := by
      have h22sq : (4.84 : ℝ) = 2.2^2 := by norm_num
      rw [h22sq, Real.sqrt_sq (by norm_num : (2.2 : ℝ) ≥ 0)]
    rw [heq] at hsq
    exact hsq
  calc phi = (1 + Real.sqrt 5) / 2 := rfl
    _ > (1 + 2.2) / 2 := by
        have h1 : 1 + Real.sqrt 5 > 1 + 2.2 := by linarith
        exact div_lt_div_of_pos_right h1 (by norm_num)
    _ = 1.6 := by norm_num

/-- Helper: φ² > 2.56 (since φ > 1.6 and 1.6² = 2.56) -/
lemma phi_sq_gt : phi ^ 2 > 2.56 := by
  have hφ : phi > 1.6 := phi_gt_16
  have hpos : 0 ≤ phi := le_of_lt phi_pos
  have h16pos : (0:ℝ) ≤ 1.6 := by norm_num
  calc phi ^ 2 = phi * phi := by ring
    _ > 1.6 * 1.6 := mul_lt_mul hφ (le_of_lt hφ) (by norm_num) hpos
    _ = 2.56 := by norm_num

/-- Helper: φ^4 > 6.5 (since φ² > 2.56 and 2.56² > 6.5) -/
lemma phi_pow4_gt : phi ^ 4 > 6.5 := by
  have h2 : phi ^ 2 > 2.56 := phi_sq_gt
  have hpos : 0 ≤ phi ^ 2 := le_of_lt (pow_pos phi_pos 2)
  have h256pos : (0:ℝ) ≤ 2.56 := by norm_num
  calc phi ^ 4 = phi ^ 2 * phi ^ 2 := by ring
    _ > 2.56 * 2.56 := mul_lt_mul h2 (le_of_lt h2) (by norm_num) hpos
    _ = 6.5536 := by norm_num
    _ > 6.5 := by norm_num

/-- Helper: φ^5 > 10 (since φ^4 > 6.5 and φ > 1.6) -/
lemma phi_pow5_gt_10 : phi ^ 5 > 10 := by
  have h4 : phi ^ 4 > 6.5 := phi_pow4_gt
  have hφ : phi > 1.6 := phi_gt_16
  have hpos : 0 ≤ phi ^ 4 := le_of_lt (pow_pos phi_pos 4)
  calc phi ^ 5 = phi ^ 4 * phi := by ring
    _ > 6.5 * 1.6 := mul_lt_mul h4 (le_of_lt hφ) (by norm_num) hpos
    _ = 10.4 := by norm_num
    _ > 10 := by norm_num

/-- Helper: φ^8 > 42 (since φ^4 > 6.5 and 6.5² = 42.25) -/
lemma phi_pow8_gt_42 : phi ^ 8 > 42 := by
  have h4 : phi ^ 4 > 6.5 := phi_pow4_gt
  have hpos : 0 ≤ phi ^ 4 := le_of_lt (pow_pos phi_pos 4)
  calc phi ^ 8 = phi ^ 4 * phi ^ 4 := by ring
    _ > 6.5 * 6.5 := mul_lt_mul h4 (le_of_lt h4) (by norm_num) hpos
    _ = 42.25 := by norm_num
    _ > 42 := by norm_num

/-- Helper: φ^40 > 10^7 (since φ^8 > 42 and 42^5 > 10^8) -/
lemma phi_pow40_gt : phi ^ 40 > 10^7 := by
  have h8 : phi ^ 8 > 42 := phi_pow8_gt_42
  have hpos : 0 ≤ phi ^ 8 := le_of_lt (pow_pos phi_pos 8)
  have h42pos : (0:ℝ) ≤ 42 := by norm_num
  -- φ^40 = (φ^8)^5 > 42^5 = 130,691,232 > 10^8 > 10^7
  -- We need to show (φ^8)^5 > 42^5 step by step
  have h16 : phi ^ 16 > 42 * 42 := by
    calc phi ^ 16 = phi ^ 8 * phi ^ 8 := by ring
      _ > 42 * 42 := mul_lt_mul h8 (le_of_lt h8) (by norm_num) hpos
  have h24 : phi ^ 24 > 42 * 42 * 42 := by
    calc phi ^ 24 = phi ^ 16 * phi ^ 8 := by ring
      _ > (42 * 42) * 42 := mul_lt_mul h16 (le_of_lt h8) (by norm_num) (le_of_lt (lt_trans (by norm_num) h16))
  have h32 : phi ^ 32 > 42 * 42 * 42 * 42 := by
    calc phi ^ 32 = phi ^ 24 * phi ^ 8 := by ring
      _ > (42 * 42 * 42) * 42 := mul_lt_mul h24 (le_of_lt h8) (by norm_num) (le_of_lt (lt_trans (by norm_num) h24))
  calc phi ^ 40 = phi ^ 32 * phi ^ 8 := by ring
    _ > (42 * 42 * 42 * 42) * 42 := mul_lt_mul h32 (le_of_lt h8) (by norm_num) (le_of_lt (lt_trans (by norm_num) h32))
    _ = 130691232 := by norm_num
    _ > 10^7 := by norm_num

/-- Saturation threshold is very large (φ^45 ≈ 2.54 × 10^9 > 10^8) -/
theorem saturationThreshold_large : SaturationThreshold > 10^8 := by
  unfold SaturationThreshold
  have hφ1 : 1 < phi := one_lt_phi
  have hφpos : 0 < phi := phi_pos
  have h5 : phi ^ 5 > 10 := phi_pow5_gt_10
  have h40 : phi ^ 40 > 10^7 := phi_pow40_gt
  calc phi ^ 45 = phi ^ 5 * phi ^ 40 := by ring
    _ > 10 * 10^7 := mul_lt_mul h5 (le_of_lt h40) (by norm_num : (0:ℝ) < 10^7) (by linarith)
    _ = 10^8 := by norm_num

/-! ## Re-embodiment Cost Model -/

/-- The "cost of non-existence" when phase density exceeds saturation.

    When patterns accumulate beyond threshold, there's an effective
    pressure that makes staying in Light Memory more expensive than
    re-embodiment.

    This inverts the usual dissolution preference. -/
noncomputable def NonExistenceCost (density : ℝ) : ℝ :=
  if density ≤ SaturationThreshold
  then 0  -- Below saturation: no pressure
  else (density - SaturationThreshold) ^ 2 / (2 * SaturationThreshold ^ 2)

/-- Non-existence cost is nonnegative -/
theorem nonExistenceCost_nonneg (density : ℝ) (hd : 0 ≤ density) :
    0 ≤ NonExistenceCost density := by
  unfold NonExistenceCost
  split_ifs with h
  · norm_num
  · push_neg at h
    -- Above saturation: quadratic cost over a positive denominator
    have hsq : 0 ≤ (density - SaturationThreshold) ^ 2 := sq_nonneg _
    have hden : 0 < 2 * SaturationThreshold ^ 2 := by
      have hpos : 0 < SaturationThreshold ^ 2 := sq_pos_of_pos saturationThreshold_pos
      exact mul_pos two_pos hpos
    exact div_nonneg hsq (le_of_lt hden)

/-- Below saturation, non-existence is free -/
theorem nonExistenceCost_zero_below (density : ℝ) (h : density ≤ SaturationThreshold) :
    NonExistenceCost density = 0 := by
  unfold NonExistenceCost
  simp [h]

/-- Above saturation, non-existence has positive cost -/
theorem nonExistenceCost_pos_above (density : ℝ) (h : density > SaturationThreshold) :
    0 < NonExistenceCost density := by
  unfold NonExistenceCost
  simp [not_le.mpr h]
  apply div_pos
  · -- numerator (density - threshold)^2 > 0
    have hpos : 0 < density - SaturationThreshold := sub_pos.mpr h
    exact sq_pos_of_pos hpos
  · -- denominator 2 * threshold^2 > 0
    have hpos : 0 < SaturationThreshold ^ 2 := sq_pos_of_pos saturationThreshold_pos
    exact mul_pos two_pos hpos

/-! ## Re-embodiment Dynamics -/

/-- Re-embodiment becomes favored when non-existence cost exceeds embodiment cost.

    For a pattern with recognition cost C_body, re-embodiment is favored when:
    NonExistenceCost > C_body -/
def ReembodimentFavored (lm : LightMemoryState) (density C_body : ℝ) : Prop :=
  NonExistenceCost density > C_body

/-- **BIRTH FROM SATURATION THEOREM**

    When phase density exceeds the saturation threshold, there exists
    a pattern for which re-embodiment is favored (assuming minimal body cost).

    This is an **existential** statement: it formalizes that, under explicit
    assumptions (saturation + a low enough embodiment cost bound), some pattern
    satisfies the favored-embodiment inequality. It does not by itself model
    inevitability or time-to-rebirth. -/
theorem birth_from_saturation
    (patterns : Finset LightMemoryState)
    (region : Region)
    (h_saturated : PhaseDensity patterns region > SaturationThreshold)
    (C_body_min : ℝ)
    (hC_small : C_body_min < NonExistenceCost (PhaseDensity patterns region)) :
    patterns.Nonempty →
    ∃ p ∈ patterns, ReembodimentFavored p (PhaseDensity patterns region) C_body_min := by
  intro hne
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, hp, hC_small⟩

/-! ## The Complete Cycle -/

/-- State in the Life-Death-Rebirth cycle -/
inductive CycleState
  | Living : StableBoundary → CycleState
  | Dissolving : StableBoundary → CycleState
  | LightMemory : LightMemoryState → CycleState
  | Saturated : LightMemoryState → ℝ → CycleState  -- pattern + density
  | Reforming : LightMemoryState → CycleState

/-- Transition relation in the cycle -/
inductive CycleTransition : CycleState → CycleState → Prop
  | dissolution (b : StableBoundary) :
      CycleTransition (.Living b) (.Dissolving b)
  | to_light (b : StableBoundary) (t : ℝ) :
      CycleTransition (.Dissolving b) (.LightMemory (toLightMemory b t))
  | saturation (lm : LightMemoryState) (d : ℝ) (h : d > SaturationThreshold) :
      CycleTransition (.LightMemory lm) (.Saturated lm d)
  | reformation (lm : LightMemoryState) (d : ℝ) :
      CycleTransition (.Saturated lm d) (.Reforming lm)
  | rebirth (lm : LightMemoryState) (b : StableBoundary)
      (hZ : Z_invariant lm.pattern = Z_invariant b.pattern) :
      CycleTransition (.Reforming lm) (.Living b)

/-- **CYCLE COMPLETENESS THEOREM**

    From any living state, there is a path back to a living state.
    This is a **path-existence** result in the abstract `CycleTransition` relation:
    it constructs witnesses (a density above threshold, and a boundary with matching Z)
    that complete the Life → Death → Light → Saturation → Rebirth → Life chain.

    It does not by itself prove that saturation occurs dynamically, nor does it
    model rates/arrival of suitable substrates. -/
theorem cycle_complete (b : StableBoundary) (t : ℝ) :
    ∃ d : ℝ, ∃ b' : StableBoundary,
      Z_invariant (toLightMemory b t).pattern = Z_invariant b'.pattern ∧
      d > SaturationThreshold ∧
      CycleTransition (.Living b) (.Dissolving b) ∧
      CycleTransition (.Dissolving b) (.LightMemory (toLightMemory b t)) ∧
      CycleTransition (.LightMemory (toLightMemory b t)) (.Saturated (toLightMemory b t) d) ∧
      CycleTransition (.Saturated (toLightMemory b t) d) (.Reforming (toLightMemory b t)) ∧
      CycleTransition (.Reforming (toLightMemory b t)) (.Living b') := by
  -- We need to show the cycle can complete
  -- Use original boundary as witness for rebirth (Z preserved)
  use SaturationThreshold + 1, b
  constructor
  · -- Z is preserved through the cycle
    rfl
  constructor
  · linarith [saturationThreshold_pos]
  constructor
  · exact .dissolution b
  constructor
  · exact .to_light b t
  constructor
  · exact .saturation (toLightMemory b t) (SaturationThreshold + 1) (by linarith)
  constructor
  · exact .reformation (toLightMemory b t) (SaturationThreshold + 1)
  · exact .rebirth (toLightMemory b t) b rfl

/-! ## Phase Pressure Dynamics -/

/-- Rate of phase density increase as patterns dissolve -/
noncomputable def dissolutionRate (living_patterns : ℕ) (death_rate : ℝ) : ℝ :=
  living_patterns * death_rate

/-- Rate of phase density decrease as patterns re-embody -/
noncomputable def rebirthRate (density : ℝ) (substrate_density : ℝ) : ℝ :=
  if density > SaturationThreshold
  then substrate_density * (density - SaturationThreshold)
  else 0

/-- **EQUILIBRIUM THEOREM**

    At equilibrium, the dissolution rate equals the rebirth rate.
    This determines the steady-state phase density of the Light Field.

    Requires at least one living pattern for non-trivial equilibrium. -/
theorem phase_equilibrium
    (living_patterns : ℕ) (death_rate substrate_density : ℝ)
    (hl : 0 < living_patterns) (hd : 0 < death_rate) (hs : 0 < substrate_density) :
    ∃ d_eq : ℝ, d_eq > SaturationThreshold ∧
      dissolutionRate living_patterns death_rate = rebirthRate d_eq substrate_density := by
  -- At equilibrium: living_patterns * death_rate = substrate_density * (d - threshold)
  -- Solving: d = threshold + (living * death_rate) / substrate_density
  let d_eq := SaturationThreshold + (living_patterns * death_rate) / substrate_density
  use d_eq
  constructor
  · -- d_eq > threshold since living_patterns > 0
    have hcast : 0 < (living_patterns : ℝ) := Nat.cast_pos.mpr hl
    have hnum : 0 < (living_patterns : ℝ) * death_rate := mul_pos hcast hd
    have hdiv : 0 < (living_patterns : ℝ) * death_rate / substrate_density := div_pos hnum hs
    linarith
  · -- rates equal at d_eq
    unfold dissolutionRate rebirthRate
    have hcast : 0 < (living_patterns : ℝ) := Nat.cast_pos.mpr hl
    have hnum : 0 < (living_patterns : ℝ) * death_rate := mul_pos hcast hd
    have hdiv : 0 < (living_patterns : ℝ) * death_rate / substrate_density := div_pos hnum hs
    -- d_eq > SaturationThreshold
    have hd_gt : d_eq > SaturationThreshold := by linarith
    -- Rewrite if-then-else using the fact that d_eq > threshold
    rw [if_pos hd_gt]
    -- Now goal is: living_patterns * death_rate = substrate_density * (d_eq - SaturationThreshold)
    -- where d_eq = SaturationThreshold + (living * death_rate) / substrate_density
    -- So d_eq - threshold = (living * death_rate) / substrate_density
    -- And substrate_density * (d_eq - threshold) = living * death_rate
    have heq : d_eq - SaturationThreshold = (living_patterns : ℝ) * death_rate / substrate_density := by
      simp only [d_eq]
      ring
    rw [heq]
    field_simp [ne_of_gt hs]

end PhaseSaturation
end Consciousness
end IndisputableMonolith
