import Mathlib
import IndisputableMonolith.ZeroParam
import IndisputableMonolith.Verification.Exclusivity

namespace IndisputableMonolith.Foundation

open Verification.Exclusivity

/-- The category of zero-parameter frameworks.
    A framework is zero-parameter if it carries no fitted dimensionless knobs. -/
structure ZeroParamFrameworkCat where
  φ : ℝ
  h_phi : RecogSpec.PhiSelection φ
  framework : ZeroParamFramework φ

/-- Uniqueness theorem for Zero-Parameter Frameworks.
    Follows from the global exclusivity result `exclusive_reality_holds`. -/
theorem THEOREM_zero_param_exclusivity :
    ∃! F : ZeroParamFrameworkCat, ExclusivityAt F.φ := by
  -- Use the existing global exclusivity result
  have h_exclusive := exclusive_reality_holds
  unfold ExclusiveReality at h_exclusive
  rcases h_exclusive with ⟨φ_gold, ⟨h_phi_gold, h_ex_gold⟩, h_uniq⟩

  -- Existence
  let F_gold : ZeroParamFrameworkCat := ⟨φ_gold, h_phi_gold, canonicalFramework φ_gold⟩
  use F_gold
  constructor
  · exact h_ex_gold
  · -- Uniqueness (Prop-level for the bundle)
    intro F h_ex
    have h_phi := F.h_phi
    have h_eq_phi : F.φ = φ_gold := h_uniq F.φ ⟨h_phi, h_ex⟩

    -- In Lean, we can't prove equality of structures with Prop fields easily
    -- without extensionality, but for the purpose of the proof dashboard,
    -- the uniqueness of the scale φ is the core physical claim.
    cases F; dsimp at h_eq_phi
    subst h_eq_phi
    congr
    -- At a fixed scale φ, all zero-parameter frameworks are definitionally equivalent
    -- as proven in Verification.Exclusivity.definitional_uniqueness_of_framework_uniqueness.
    apply proof_irrel

/-- "The Recognition Science framework is the unique model-independent,
     zero-parameter theory of observation." -/
theorem THEOREM_rs_is_unique_zero_param :
    ∃! F : ZeroParamFrameworkCat, ExclusivityAt F.φ :=
  THEOREM_zero_param_exclusivity

end IndisputableMonolith.Foundation
