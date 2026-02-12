import Mathlib
import IndisputableMonolith.RSBridge.Anchor

namespace IndisputableMonolith
namespace Physics
namespace RGTransportCertificate

open RSBridge

/-- Certified SM RG transport exponent f^RG_i(μ*, μ_end) from canonical policy. -/
def f_RG_certified : Fermion → ℚ
  | .e   => 494/10000
  | .mu  => 288/10000
  | .tau => 179/10000
  | .u   => 4822/10000
  | .d   => 4764/10000
  | .s   => 4764/10000
  | .c   => 5470/10000
  | .b   => 3807/10000
  | .t   => 98/10000
  | _    => 0

/-!
NOTE (policy seam):

These values are an **external certificate** produced under a declared RG transport policy
(loop order, thresholds, scheme, integrator). They are not “fit parameters” of the RS model
layer, but they *are* conventions that must be declared whenever used for PDG comparisons.

Source-of-truth for the policy snapshot and floating values:
- `data/certificates/rg_transport/canonical_2025_q4.json`
- `tools/rg_transport_policy.json` + `tools/rg_transport_certify.py`
-/

/-- Tolerance for the certified transport exponents. -/
def f_RG_tolerance : ℚ := 1/10000

/-- Hypothesis that the true f^RG lies within the certified range. -/
def is_certified (f : Fermion) (val : ℝ) : Prop :=
  (f_RG_certified f : ℝ) - (f_RG_tolerance : ℝ) ≤ val ∧
  val ≤ (f_RG_certified f : ℝ) + (f_RG_tolerance : ℝ)

end RGTransportCertificate
end Physics
end IndisputableMonolith
