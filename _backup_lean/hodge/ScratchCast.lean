import Hodge.Cohomology.Basic

namespace ScratchCast

open Classical
open Hodge

set_option autoImplicit false

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

example {k : ℕ} (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    (Quotient.mk _ ({ val := ω, property := hω } : ClosedForm n X k) : DeRhamCohomologyClass n X k) =
      (⟦ω, hω⟧ : DeRhamCohomologyClass n X k) := by
  rfl

end ScratchCast
