import Mathlib
import IndisputableMonolith.Verification.CPMBridge.Universality
import IndisputableMonolith.Verification.CPMBridge.DomainCertificates.Hodge
import IndisputableMonolith.Verification.CPMBridge.DomainCertificates.Goldbach
import IndisputableMonolith.Verification.CPMBridge.DomainCertificates.RiemannHypothesis
import IndisputableMonolith.Verification.CPMBridge.DomainCertificates.NavierStokes
import IndisputableMonolith.Verification.CPMBridge.Constants.Probability

namespace IndisputableMonolith
namespace Verification
namespace CPMBridge

/-- Convenience namespace that exports the CPM universality bridge and supporting modules. -/
def moduleSummary : String :=
  "CPMBridge aggregates universality, certificates, and probability bounds."

end CPMBridge
end Verification
end IndisputableMonolith
