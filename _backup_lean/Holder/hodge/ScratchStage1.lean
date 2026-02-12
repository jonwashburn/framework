import Hodge.Analytic.DistributionTestForms
import Hodge.Analytic.Stage1.TestFunctionDeriv

open scoped Distributions

namespace ScratchStage1

open Classical TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : TopologicalSpace.Opens E}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

#check TestFunction.mkCLM
#check Hodge.Analytic.Stage1.iteratedFDerivTestFunction

-- try to define a CLM into test functions of derivatives
noncomputable def derivCLM : 𝓓(Ω, F) →L[ℝ] 𝓓(Ω, Hodge.Analytic.Stage1.IteratedFDerivTarget (E := E) (F := F) 1) := by
  classical
  -- attempt using mkCLM
  refine TestFunction.mkCLM ℝ (fun f => Hodge.Analytic.Stage1.iteratedFDerivTestFunction (Ω := Ω) (F := F) 1 f)
    (fun f g => ?_) (fun c f => ?_) (fun K Ksub => ?_)
  · ext x; rfl
  · ext x; rfl
  · -- continuity on each compact support piece
    -- TODO
    simpa using (continuous_const)

end ScratchStage1
