import Mathlib

namespace IndisputableMonolith
namespace YM

noncomputable section
open Classical Complex

structure TransferKernel (ι : Type) where
  T : (ι → ℂ) →L[ℂ] (ι → ℂ)

structure MatrixView (ι : Type) [Fintype ι] [DecidableEq ι] where
  A : Matrix ι ι ℂ

noncomputable def CLM.ofLM {ι : Type}
  (L : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
{ toLinearMap := L, cont := by exact ContinuousLinearMap.continuous _ }

structure MatrixBridge (ι : Type) [Fintype ι] [DecidableEq ι]
  (K : TransferKernel ι) (V : MatrixView ι) where
  intertwine : K.T = CLM.ofLM (Matrix.toLin' V.A)

def KernelHasMatrixView (ι : Type) [Fintype ι] [DecidableEq ι]
  (K : TransferKernel ι) (V : MatrixView ι) : Prop :=
  Nonempty (MatrixBridge ι K V)

noncomputable def buildKernelFromMatrix (ι : Type) [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) : Σ K : TransferKernel ι, MatrixBridge ι K V :=
by
  let K : TransferKernel ι := { T := CLM.ofLM (Matrix.toLin' V.A) }
  exact ⟨K, { intertwine := rfl }⟩

noncomputable def constantStochastic3x3 : MatrixView (Fin 3) :=
{ A := fun _ _ => ((1/3 : ℝ) : ℂ) }

noncomputable def kernel3x3_with_bridge :
  Σ K : TransferKernel (Fin 3), MatrixBridge (Fin 3) K constantStochastic3x3 :=
  buildKernelFromMatrix (ι := Fin 3) constantStochastic3x3

end
end YM
end IndisputableMonolith
