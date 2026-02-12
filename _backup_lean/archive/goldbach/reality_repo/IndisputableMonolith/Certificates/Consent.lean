import Mathlib
import IndisputableMonolith.LNAL.Compiler

namespace IndisputableMonolith
namespace Certificates

open IndisputableMonolith
open IndisputableMonolith.LNAL

/-- ConsentDerivative audit certificate summarising static gate status. -/
structure ConsentCert where
  enabled    : Bool
  ok         : Bool
  violations : List Nat := []
  messages   : List String := []
deriving Repr

@[simp] def ConsentCert.verified (c : ConsentCert) : Prop := c.ok = true

def ConsentCert.fromReport (report : CompileReport) : ConsentCert :=
  { enabled := report.consent.enabled,
    ok := report.consent.ok,
    violations := report.consent.violations,
    messages :=
      if report.consent.enabled then
        if report.consent.ok then []
        else ["ConsentDerivative gate violated"]
      else if report.consent.violations.isEmpty then []
      else ["ConsentDerivative gate disabled; potential violations detected"] }

noncomputable def ConsentCert.fromSource (src : String) (enableGate : Bool := false) : ConsentCert :=
  let (report, _) := compile src enableGate
  fromReport report

end Certificates
end IndisputableMonolith
