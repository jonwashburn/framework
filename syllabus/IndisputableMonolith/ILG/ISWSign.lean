import Mathlib
import IndisputableMonolith.ILG.Kernel
import IndisputableMonolith.ILG.GrowthODE

namespace IndisputableMonolith
namespace ILG

open Real

/-!
# ISW Sign Proof

This module formalizes the sign logic for the Integrated Sachs-Wolfe (ISW) driver
B(a,k). A positive driver B combined with a negative gravitational potential Phi
predicts a negative CMB-LSS cross-correlation at low multipoles.

## References
- `Papers-tex/Gravity Set/Dark-Energy.tex`: "Because f > 1 and ∂lnw > 0 at late time,
  the bracket is positive while Phi < 0, yielding a negative CMB–galaxy correlation."
-/

/-- The ISW driver B(a,k) = -1 + f + dlnw/dlna. -/
noncomputable def isw_driver (P : KernelParams) (k a : ℝ) : ℝ :=
  let f := f_growth_eds_ilg P k a
  let Xinv := a / (k * P.tau0)
  let dlnw := (P.alpha * P.C * Xinv ^ P.alpha) / (1 + P.C * Xinv ^ P.alpha)
  -1 + f + dlnw

/-- Lemma: In ILG baseline, the growth rate f is greater than 1. -/
theorem f_growth_gt_one (P : KernelParams) (k a : ℝ) (ha : 0 < a) (hk : 0 < k)
    (halpha : 0 < P.alpha) (hC : 0 < P.C) :
    1 < f_growth_eds_ilg P k a := by
  set Xinv := a / (k * P.tau0)
  set B := growth_prefactor P.alpha P.C
  have hB : 0 < B := by
    unfold growth_prefactor
    apply div_pos
    · linarith
    · nlinarith
  have hXinv : 0 < Xinv := div_pos ha (mul_pos hk P.tau0_pos)
  have hXinv_pow : 0 < Xinv ^ P.alpha := rpow_pos_of_pos hXinv _
  unfold f_growth_eds_ilg
  -- f = (1 + B(1+alpha)X^alpha) / (1 + BX^alpha)
  -- 1 < (1 + BX^alpha + B*alpha*X^alpha) / (1 + BX^alpha)
  -- 1 < 1 + (B*alpha*X^alpha) / (1 + BX^alpha)
  field_simp
  apply lt_add_of_pos_right
  apply div_pos
  · repeat apply mul_pos <;> assumption
  · apply add_pos_of_pos_of_nonneg
    · exact one_pos
    · repeat apply mul_nonneg <;> (try exact le_of_lt hB) <;> (try exact le_of_lt hXinv_pow)

/-- Lemma: In ILG baseline, the kernel log-derivative dlnw/dlna is positive. -/
theorem dlnw_pos (P : KernelParams) (k a : ℝ) (ha : 0 < a) (hk : 0 < k)
    (halpha : 0 < P.alpha) (hC : 0 < P.C) :
    0 < (P.alpha * P.C * (a / (k * P.tau0)) ^ P.alpha) / (1 + P.C * (a / (k * P.tau0)) ^ P.alpha) := by
  set Xinv := a / (k * P.tau0)
  have hXinv : 0 < Xinv := div_pos ha (mul_pos hk P.tau0_pos)
  have hXinv_pow : 0 < Xinv ^ P.alpha := rpow_pos_of_pos hXinv _
  apply div_pos
  · repeat apply mul_pos <;> assumption
  · apply add_pos_of_pos_of_nonneg
    · exact one_pos
    · repeat apply mul_nonneg <;> (try exact le_of_lt hC) <;> (try exact le_of_lt hXinv_pow)

/-- Main Theorem (Target E): The ISW driver B(a,k) is strictly positive in ILG baseline. -/
theorem isw_driver_positive (P : KernelParams) (k a : ℝ) (ha : 0 < a) (hk : 0 < k)
    (halpha : 0 < P.alpha) (hC : 0 < P.C) :
    0 < isw_driver P k a := by
  unfold isw_driver
  have hf := f_growth_gt_one P k a ha hk halpha hC
  have hd := dlnw_pos P k a ha hk halpha hC
  linarith

end ILG
end IndisputableMonolith
