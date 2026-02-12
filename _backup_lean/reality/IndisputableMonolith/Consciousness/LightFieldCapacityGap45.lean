import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gap45.Derivation
import IndisputableMonolith.Consciousness.LightFieldDensity
import IndisputableMonolith.Consciousness.LightFieldStability

/-!
# Light-Field Capacity Bridge (Gap-45 / φ-scaling) — Conditional Spine

Discovery posture:
- This file does **not** assert that the Light Field is physically real or finite.
- It isolates the *minimal explicit hypotheses* needed to turn a geometric packing bound
  into a specific φ-exponent capacity scale, and then connects that scale to `φ^45`
  via the existing Gap-45 integer.

Status:
- The pure math spine (packing bound from separation in 1D intervals) is proved in
  `LightFieldStability.lean`.
- The RS-specific bridge (why the relevant depth is 45 and why separation scales as φ^{-n})
  is recorded here as **explicit hypotheses**.
-/

namespace IndisputableMonolith
namespace Consciousness

open Constants

namespace LightFieldCapacityGap45

/-! ## Hypotheses (explicit; these are the RS-specific bridge points) -/

/--
Hypotheses needed to connect:

1) a **closure depth** (an integer) to Gap-45, and
2) a **φ-scaling minimum separation** law to a capacity-per-unit-length scale.

These are *not* currently derivable from the existing Light Memory formalization; they
are written explicitly so we can (a) minimize them, and (b) later try to discharge them
from stronger RS structures.
-/
structure CapacityHypotheses where
  /-- The relevant discretization/closure depth for Light Memory addressing. -/
  closureDepth : ℕ

  /-- Bridge claim (H3): this depth coincides with the Gap-45 construction. -/
  closureDepth_eq_gap : closureDepth = Gap45.Derivation.gap

  /-- A minimum separation scale `r_min` (in the 1D Light Field coordinate). -/
  r_min : ℝ
  r_min_pos : 0 < r_min

  /--
  Bridge claim (H4): φ-scaling separation law.

  Interpreting closure depth as a refinement level, the minimum separation shrinks
  geometrically as `φ^{-closureDepth}` (in chosen units).
  -/
  r_min_eq_phi_inv_pow : r_min = (phi ^ closureDepth)⁻¹

/-! ## Derived threshold from the hypotheses -/

/-- Derived capacity scale (patterns per unit length) from `r_min`. -/
noncomputable def DerivedSaturationThreshold (H : CapacityHypotheses) : ℝ :=
  1 / H.r_min

theorem derivedThreshold_pos (H : CapacityHypotheses) : 0 < DerivedSaturationThreshold H := by
  unfold DerivedSaturationThreshold
  exact one_div_pos.mpr H.r_min_pos

/-- Under the φ-scaling hypothesis, the derived threshold equals `φ^{closureDepth}`. -/
theorem derivedThreshold_eq_phi_pow_depth (H : CapacityHypotheses) :
    DerivedSaturationThreshold H = phi ^ H.closureDepth := by
  unfold DerivedSaturationThreshold
  -- 1 / r_min = 1 / (φ^depth)⁻¹ = φ^depth
  -- Use the hypothesis to rewrite `r_min`.
  rw [H.r_min_eq_phi_inv_pow]
  -- `1 / x⁻¹ = x` for nonzero x.
  have hne : (phi ^ H.closureDepth) ≠ 0 := by
    exact pow_ne_zero _ (ne_of_gt phi_pos)
  field_simp [hne]

/-- The derived threshold equals `φ^gap`. -/
theorem derivedThreshold_eq_phi_pow_gap (H : CapacityHypotheses) :
    DerivedSaturationThreshold H = phi ^ Gap45.Derivation.gap := by
  -- rewrite closureDepth to gap
  simpa [H.closureDepth_eq_gap] using (derivedThreshold_eq_phi_pow_depth H)

/-- Since `gap = 45`, the derived threshold equals `φ^45`. -/
theorem derivedThreshold_eq_phi_pow_45 (H : CapacityHypotheses) :
    DerivedSaturationThreshold H = phi ^ 45 := by
  -- Use gap_eq_45 (simp theorem) to rewrite.
  simpa [Gap45.Derivation.gap_eq_45] using (derivedThreshold_eq_phi_pow_gap H)

/-! ## Capacity bound from separation (connect to the packing theorem) -/

/--
`StableInInterval` is the concrete “capacity” stability predicate for located patterns:
they lie in the region and are separated by at least `r_min`.

This is deliberately geometric; it does **not** mention `φ^45`.
-/
def StableInInterval (H : CapacityHypotheses) (patterns : Finset LocatedLightMemory) (R : IntervalRegion) : Prop :=
  InInterval patterns R ∧ RSeparated patterns H.r_min

/--
From stability, we obtain the packing inequality:

\[
(\#patterns - 1)\, r_{min} \le \mathrm{vol}(R).
\]
-/
theorem packing_ineq_of_stable
    (H : CapacityHypotheses)
    (patterns : Finset LocatedLightMemory)
    (R : IntervalRegion)
    (hne : patterns.Nonempty)
    (hst : StableInInterval H patterns R) :
    ((patterns.card : ℝ) - 1) * H.r_min ≤ R.volume := by
  rcases hst with ⟨hin, hsep⟩
  -- Build the step-separated witness from pairwise separation and apply the packing theorem.
  have hw : Nonempty (Packing1D.StepSeparatedWitness patterns R H.r_min) :=
    Packing1D.stepSeparatedWitness_of_rSeparated patterns R H.r_min H.r_min_pos hin hsep
  rcases hw with ⟨w⟩
  exact Packing1D.span_ge_card_mul_stepSep patterns R H.r_min w hne

/--
An explicit (loose but simple) density upper bound derived from stability:

\[
\mathrm{density} \le \frac{1}{r_{min}} + \frac{1}{\mathrm{vol}(R)}.
\]

This is the bridge from geometric separation to a “capacity per unit length” scale.
-/
theorem density_le_one_div_rmin_add_one_div_vol
    (H : CapacityHypotheses)
    (patterns : Finset LocatedLightMemory)
    (R : IntervalRegion)
    (hne : patterns.Nonempty)
    (hst : StableInInterval H patterns R) :
    densityInInterval patterns R ≤
      (1 / H.r_min) + (1 / R.volume) := by
  -- Start from the packing inequality.
  have hpack := packing_ineq_of_stable H patterns R hne hst
  have hrpos : 0 < H.r_min := H.r_min_pos
  have hvpos : 0 < R.volume := R.volume_pos
  -- Rearrange: (card-1)*r ≤ vol  ⇒  card/vol ≤ 1/r + 1/vol.
  -- We do this algebraically with `nlinarith`.
  unfold densityInInterval countInInterval
  -- `countInInterval patterns R ≤ patterns.card`, so replace count with card for an upper bound.
  -- This step avoids additional bookkeeping about filters.
  classical
  have hcount_le : (countInInterval patterns R : ℝ) ≤ (patterns.card : ℝ) := by
    -- filter.card ≤ card
    have : countInInterval patterns R ≤ patterns.card := by
      -- `card_filter_le` is in Mathlib
      simpa [countInInterval] using (Finset.card_filter_le (s := patterns) (p := fun p => decide (R.Contains p.pos)))
    exact_mod_cast this
  -- Now bound density by card/vol and use the packing inequality.
  have hdens_le : (countInInterval patterns R : ℝ) / R.volume ≤ (patterns.card : ℝ) / R.volume := by
    exact div_le_div_of_nonneg_right hcount_le (le_of_lt hvpos)
  have hcard_le : (patterns.card : ℝ) / R.volume ≤ (1 / H.r_min) + (1 / R.volume) := by
    -- From hpack: ((card:ℝ)-1)*r ≤ vol, derive:
    -- card/vol ≤ 1/r + 1/vol.
    have hv : 0 < R.volume := hvpos
    have hr : 0 < H.r_min := hrpos
    -- First show: (card-1)/vol ≤ 1/r.
    have hcore : ((patterns.card : ℝ) - 1) / R.volume ≤ 1 / H.r_min := by
      -- From hpack: ((card-1)*r ≤ vol) we get (card-1) ≤ vol / r (since r>0),
      -- then divide by vol>0 to get (card-1)/vol ≤ 1/r.
      have h_le_div : ((patterns.card : ℝ) - 1) ≤ R.volume / H.r_min :=
        (le_div_iff₀ hr).2 hpack
      -- Divide both sides by vol (positive).
      have h_div : ((patterns.card : ℝ) - 1) / R.volume ≤ (R.volume / H.r_min) / R.volume :=
        (div_le_div_of_nonneg_right h_le_div (le_of_lt hv))
      -- Simplify RHS: (vol / r) / vol = 1 / r.
      have hvne : R.volume ≠ 0 := ne_of_gt hv
      have hrne : H.r_min ≠ 0 := ne_of_gt hr
      -- (vol / r) / vol = vol / (r * vol) = 1 / r (by cancellation of vol).
      -- We use `mul_div_mul_left` after rewriting as (vol*1)/(vol*r).
      have hsimp : (R.volume / H.r_min) / R.volume = 1 / H.r_min := by
        -- Expand divisions and cancel `R.volume`.
        -- `field_simp` is safe here because `R.volume ≠ 0` and `r_min ≠ 0`.
        field_simp [hvne, hrne]
      simpa [hsimp] using h_div
    -- Now: card/vol = (card-1)/vol + 1/vol
    calc
      (patterns.card : ℝ) / R.volume
          = (patterns.card : ℝ) * R.volume⁻¹ := by simp [div_eq_mul_inv]
      _ = ((patterns.card : ℝ) - 1) * R.volume⁻¹ + R.volume⁻¹ := by ring
      _ ≤ (1 / H.r_min) + R.volume⁻¹ := by
          -- add the same `1/vol` term to both sides (right-addition in this toolchain)
          have : ((patterns.card : ℝ) - 1) * R.volume⁻¹ ≤ 1 / H.r_min := by
            -- this is exactly `hcore`, rewritten into `* inv` form
            simpa [div_eq_mul_inv] using hcore
          exact add_le_add_left this _
      _ = (1 / H.r_min) + (1 / R.volume) := by simp [div_eq_mul_inv]
  exact le_trans hdens_le hcard_le

end LightFieldCapacityGap45

end Consciousness
end IndisputableMonolith
