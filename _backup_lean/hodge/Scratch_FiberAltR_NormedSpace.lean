import Hodge.Basic
import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
Scratch: check whether `FiberAltR := (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ` carries a `NormedSpace ℂ`
instance (so we could plausibly redefine `FiberAlt` without breaking the `ContMDiff`-based `SmoothForm` layer).
-/

noncomputable section

open scoped Manifold

namespace Scratch

-- Minimal instantiation (n=1,k=1) just to trigger typeclass search.
variable (n k : ℕ)

-- If this fails, we do NOT have a bundled `NormedSpace ℂ` instance for real-alternating maps,
-- and redefining `FiberAlt` will require additional instance work.
#check (by
  let n : ℕ := 1
  let k : ℕ := 1
  -- Real-alternating, complex-valued continuous alternating maps on ℂⁿ (as a real normed space):
  haveI : NormedSpace ℂ ((TangentModel n) [⋀^Fin k]→L[ℝ] ℂ) := by infer_instance
  exact (inferInstance : NormedSpace ℂ ((TangentModel n) [⋀^Fin k]→L[ℝ] ℂ)))

-- Also check that we can take an exterior derivative on model space with `𝕜 := ℝ` and `E := ℂⁿ` (as real).
#check (by
  let n : ℕ := 1
  let k : ℕ := 1
  -- A real k-form on the model space: ℂⁿ → (ℂⁿ) [⋀^k]→L[ℝ] ℂ
  let ω : (TangentModel n) → (TangentModel n) [⋀^Fin k]→L[ℝ] ℂ := fun _ => 0
  -- Its exterior derivative exists in Mathlib:
  let dω := _root_.extDeriv (𝕜 := ℝ) (E := TangentModel n) (F := ℂ) (n := k) ω
  exact dω)

end Scratch
