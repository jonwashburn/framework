import Mathlib
import IndisputableMonolith.CPM.LawOfExistence

/-!
# J-cost Normalization Certificate

This audit certificate packages the **log-coordinate normalization** of the RS cost kernel:

\[
  \frac{d^2}{dt^2}\big(J(\exp t)\big)\Big|_{t=0} = 1.
\]

This normalization is referenced in the CPM bridge layer (e.g. the projection constant
`C_proj = 2` justification hook). Certifying it makes the “J''(1)=1” convention explicit
and machine-checked in the certified surface.
-/

namespace IndisputableMonolith
namespace Verification
namespace JcostNormalization

open IndisputableMonolith.Cost

structure JcostNormalizationCert where
  deriving Repr

@[simp] def JcostNormalizationCert.verified (_c : JcostNormalizationCert) : Prop :=
  deriv (deriv (fun t : ℝ => IndisputableMonolith.Cost.Jcost (Real.exp t))) 0 = 1

@[simp] theorem JcostNormalizationCert.verified_any (c : JcostNormalizationCert) :
    JcostNormalizationCert.verified c := by
  simpa using IndisputableMonolith.CPM.LawOfExistence.RS.Jcost_log_second_deriv_normalized

end JcostNormalization
end Verification
end IndisputableMonolith

