import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
This file is a **local overlay** used by the Hodge project.

Mathlib currently provides `AlternatingMap.domCoprod` (algebraic wedge product), but does not yet
package a corresponding `ContinuousAlternatingMap` construction in the version pinned by this repo.

To avoid polluting the main development with unfinished topology/norm arguments, we expose an
opaque interface here. Downstream files can import this module and use the wedge product as a
black box while the analytic continuity proofs are completed.

When upstream Mathlib gains a proper `ContinuousAlternatingMap.domCoprod`, this file should be
deleted and imports updated accordingly.
-/

open TensorProduct

namespace ContinuousAlternatingMap

variable {𝕜 : Type*} [NormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable [TopologicalSpace (F ⊗[𝕜] G)]

/-- **Wedge product** for continuous alternating maps (opaque placeholder).

This is intended to agree with `AlternatingMap.domCoprod` after forgetting continuity and
reindexing via `finSumFinEquiv`. -/
opaque domCoprod {k l : ℕ}
    (ω : ContinuousAlternatingMap 𝕜 E F (Fin k))
    (η : ContinuousAlternatingMap 𝕜 E G (Fin l)) :
    ContinuousAlternatingMap 𝕜 E (F ⊗[𝕜] G) (Fin (k + l))

end ContinuousAlternatingMap
