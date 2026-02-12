import Hodge.Cohomology.Basic

namespace ScratchQuotient2

open Classical
open Hodge

set_option autoImplicit false

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X]

-- no `*` notation; unfold by hand
example {k l : ℕ} (a : ClosedForm n X k) (b : ClosedForm n X l) :
    (Hodge.instHMulDeRhamCohomologyClass (n := n) (X := X) k l).hMul (Quotient.mk _ a) (Quotient.mk _ b)
      = (⟦a.val ⋏ b.val, isFormClosed_wedge _ _ a.property b.property⟧ : DeRhamCohomologyClass n X (k + l)) := by
  simp [Hodge.instHMulDeRhamCohomologyClass, Hodge.ofForm]

end ScratchQuotient2
