import Mathlib
import IndisputableMonolith.ILG.Kernel
import IndisputableMonolith.Relativity.Cosmology.FRWMetric

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

open Real

/-!
# Optical Rescaling Extension (Upsilon Route)

This module formalizes the optical rescaling route for ILG. In this route,
the Einstein equations remain unchanged, but the Ricci focusing term in
the Sachs equation is rescaled by a factor Upsilon(a).

## References
- `Papers-tex/Gravity Set/Dark-Energy.tex`: "(ii) an optical rescaling Upsilon(a)
  of the Ricci focusing in the Sachs equation that preserves metricity and
  Etherington duality while producing a mild late–time demagnification."
-/

/-- The optical rescaling factor Upsilon(a).
    It gains an ILG enhancement at late times, modifying Ricci focusing. -/
noncomputable def Upsilon (P : ILG.KernelParams) (a : ℝ) : ℝ :=
  if a ≤ 0 then 1 else 1 + P.C * a ^ P.alpha

/-- The modified Sachs focusing equation (Target G).
    For angular diameter distance D_A along an affine parameter λ:
    d²D_A/dλ² + (1/2) * Upsilon(a) * R_μν k^μ k^ν * D_A = 0
    where Ricci focusing is rescaled by Upsilon. -/
def SachsEquation_Extended (P : ILG.KernelParams) (z : ℝ) (DA_func : ℝ → ℝ) (ricci_focusing : ℝ) : Prop :=
  let a := 1 / (1 + z)
  -- Simplified ODE form in terms of z or λ
  ∀ z', deriv (deriv DA_func) z' + (Upsilon P a) * ricci_focusing * DA_func z' = 0

/-- Angular diameter distance D_A under optical rescaling.
    Modeled as the background distance rescaled by the Upsilon factor. -/
noncomputable def DA_rescaled (z : ℝ) (bg_DA : ℝ) (P : ILG.KernelParams) : ℝ :=
  -- Scale factor a = 1 / (1 + z)
  bg_DA * (1 / sqrt (Upsilon P (1 / (1 + z))))

/-- Luminosity distance D_L under optical rescaling.
    To preserve Etherington duality, it must scale identically to D_A. -/
noncomputable def DL_rescaled (z : ℝ) (bg_DL : ℝ) (P : ILG.KernelParams) : ℝ :=
  -- Etherington duality: D_L = (1 + z)^2 * D_A
  DA_rescaled z (bg_DL / (1 + z)^2) P * (1 + z)^2

/-- Main Theorem (Target G): Etherington duality is preserved under optical rescaling.
    Regardless of the Upsilon rescaling, D_L = (1 + z)^2 * D_A remains satisfied. -/
theorem etherington_duality_preserved (z : ℝ) (bg_DA bg_DL : ℝ) (P : ILG.KernelParams)
    (h_bg_dual : bg_DL = (1 + z)^2 * bg_DA) :
    DL_rescaled z bg_DL P = (1 + z)^2 * DA_rescaled z bg_DA P := by
  unfold DL_rescaled
  rw [h_bg_dual]
  field_simp
  ring

/-- Theorem: Optical rescaling reduces to GR when the coupling C = 0. -/
theorem optical_reduces_to_gr (z : ℝ) (bg_DA : ℝ) (P : ILG.KernelParams)
    (hC : P.C = 0) :
    DA_rescaled z bg_DA P = bg_DA := by
  unfold DA_rescaled Upsilon
  simp [hC]

end Cosmology
end Relativity
end IndisputableMonolith
