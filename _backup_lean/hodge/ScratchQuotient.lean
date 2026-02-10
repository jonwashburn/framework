import Hodge.Cohomology.Basic

namespace ScratchQuotient

open Classical
open Hodge

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]
  [ProjectiveComplexManifold n X]

-- Try simplifying a product of mk's
example {k l : ℕ} (a : ClosedForm n X k) (b : ClosedForm n X l) :
    (( (Quotient.mk _ a : DeRhamCohomologyClass n X k) * (Quotient.mk _ b : DeRhamCohomologyClass n X l) ) :
        DeRhamCohomologyClass n X (k + l))
      = (⟦a.val ⋏ b.val, isFormClosed_wedge _ _ a.property b.property⟧ : DeRhamCohomologyClass n X (k+l)) := by
  simp [Hodge.instHMulDeRhamCohomologyClass]

end ScratchQuotient
