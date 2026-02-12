import Hodge.Cohomology.Basic

noncomputable section

open Classical

namespace Hodge.WorkInProgress

universe u

variable {n : ℕ}

/-! WIP instances for the model space `TangentModel n`.

These are placeholders needed to model chart-level pushforward/pullback of currents.
They are **not** used on the proof track.
-/

instance instHasLocallyConstantCharts_TangentModel :
    HasLocallyConstantCharts n (TangentModel n) := by
  classical
  refine ⟨?_⟩
  intro x y hy
  -- chartAt on the model space is the identity chart, so it is constant.
  simp [chartAt_self_eq]

instance instCompactSpace_TangentModel : CompactSpace (TangentModel n) := by
  -- TODO: Euclidean space is not compact; this is a WIP placeholder.
  sorry

instance instProjectiveComplexManifold_TangentModel :
    ProjectiveComplexManifold n (TangentModel n) := by
  classical
  let p0 : ProjSpace 0 :=
    Quot.mk _ ⟨fun _ => (1 : ℂ), by
      intro h0
      have : (1 : ℂ) = 0 := by
        simpa using congrArg (fun f => f 0) h0
      exact one_ne_zero this⟩
  refine
    { embedding_dim := 0
      embedding := fun _ => p0
      embedding_continuous := by
        simpa using (continuous_const : Continuous (fun _ : TangentModel n => p0)) } <;>
  -- TODO: fill remaining fields (`IsManifold`, `CompactSpace`, `HasLocallyConstantCharts`).
  sorry

instance instKahlerManifold_TangentModel :
    KahlerManifold n (TangentModel n) := by
  classical
  -- TODO: define the standard Kähler form on ℂⁿ and prove required properties.
  sorry

end Hodge.WorkInProgress
