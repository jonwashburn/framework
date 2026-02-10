import Mathlib
import IndisputableMonolith.Relativity.Cosmology.FRWMetric

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology

/-!
# Buchert Backreaction Cancellation

This module formalizes the algebraic cancellation of the Buchert kinematical
backreaction term Q_D for irrotational potential flow.

## References
- `Papers-tex/Gravity Set/Dark-Energy.tex`: "The Buchert kinematical backreaction Q_D
  cancels mode–by–mode for potential flow even when f depends on k; thus ILG does
  not alter H(a) by averaging."
-/

/-- Buchert's kinematical backreaction term Q_D (local/mode-by-mode version).
    Q_D = (2/3) * theta^2 - 2 * sigma^2.
    Note: The ⟨θ²⟩ - ⟨θ⟩² term reduces to theta^2 in the irrotational potential flow
    limit described in the paper. -/
def localBackreaction (θ σ2 : ℝ) : ℝ :=
  (2/3 : ℝ) * θ^2 - 2 * σ2

/-- Theorem: For irrotational potential flow, the local backreaction vanishes.
    From the manuscript:
    - θ_pec = -H * f * δ
    - σ^2 = (1/3) * H^2 * f^2 * δ^2
-/
theorem buchert_cancellation (H f δ : ℝ) :
    let θ := -H * f * δ
    let σ2 := (1/3 : ℝ) * (H * f * δ)^2
    localBackreaction θ σ2 = 0 := by
  dsimp
  unfold localBackreaction
  field_simp
  ring

/-- The "No Background Modification" result: because Q_D = 0, the background
    expansion (H) remains that of the chosen matter content. -/
def no_background_modification (H f δ : ℝ) : Prop :=
  localBackreaction (-H * f * δ) ((1/3 : ℝ) * (H * f * δ)^2) = 0

theorem background_is_stable (H f δ : ℝ) : no_background_modification H f δ :=
  buchert_cancellation H f δ

end Cosmology
end Relativity
end IndisputableMonolith
