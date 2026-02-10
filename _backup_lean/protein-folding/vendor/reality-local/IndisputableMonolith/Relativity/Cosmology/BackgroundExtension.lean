import Mathlib
import IndisputableMonolith.ILG.Kernel
import IndisputableMonolith.Relativity.Cosmology.Friedmann

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

open Real

/-!
# Background Extension (w_bg Route)

This module formalizes the background form-factor extension route for ILG.
In this route, the Friedmann equations are modified by a factor w_bg(a)
multiplying the matter source.

## References
- `Papers-tex/Gravity Set/Dark-Energy.tex`: "(i) a background form–factor w_bg(a)
  multiplying the matter source in the Friedmann equations with an early–time gate
  and a fixed late–time slope tied to alpha."
-/

/-- The background extension form-factor w_bg(a).
    It is gated to unity at early times (a → 0) and gains an ILG-proportional
    enhancement at late times. -/
noncomputable def w_bg (P : ILG.KernelParams) (a : ℝ) : ℝ :=
  if a ≤ 0 then 1 else 1 + P.C * a ^ P.alpha

/-- Modified Friedmann I equation with the background extension. -/
def FriedmannI_Extended (scale : ScaleFactor) (rho_matter : ℝ → ℝ) (P : ILG.KernelParams) : Prop :=
  ∀ t, let a := scale.a t
       let H := hubble_parameter scale t
       H^2 = (8 * Real.pi / 3) * (rho_matter t * w_bg P a)

/-- Theorem: The extended Friedmann equation reduces to standard GR when C = 0. -/
theorem extended_reduces_to_gr (scale : ScaleFactor) (rho_matter : ℝ → ℝ) (P : ILG.KernelParams)
    (hC : P.C = 0) :
    FriedmannI_Extended scale rho_matter P ↔
    (∀ t, (hubble_parameter scale t)^2 = (8 * Real.pi / 3) * rho_matter t) := by
  constructor
  · intro h t
    specialize h t
    unfold w_bg at h
    simp [hC] at h
    exact h
  · intro h t
    specialize h t
    unfold w_bg
    simp [hC]
    exact h

/-- Lemma: w_bg is greater than 1 for positive scale factor and coupling. -/
theorem w_bg_gt_one (P : ILG.KernelParams) (a : ℝ) (ha : 0 < a)
    (halpha : 0 < P.alpha) (hC : 0 < P.C) :
    1 < w_bg P a := by
  unfold w_bg
  simp [ha.le, ha]
  apply lt_add_of_pos_right
  apply mul_pos hC (rpow_pos_of_pos ha P.alpha)

end Cosmology
end Relativity
end IndisputableMonolith
