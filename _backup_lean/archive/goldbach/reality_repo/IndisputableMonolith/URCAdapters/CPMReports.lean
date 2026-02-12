import Mathlib
import IndisputableMonolith.CPM.LawOfExistence
import IndisputableMonolith.Verification.CPMBridge.Initiality

/-!
# URC Adapters: CPM Universality Reports

This module provides simple, machine-readable checks and pretty printers
to audit CPM universality across domain instantiations and to compare
constants against the RS cone-projection core invariants.
-/

namespace IndisputableMonolith
namespace URCAdapters
namespace CPMReports

open IndisputableMonolith.CPM.LawOfExistence
open IndisputableMonolith.Verification.CPMBridge.Initiality

/-- A compact string representation of `(Knet, Cproj)` for quick reports. -/
noncomputable def coreSummary (C : Constants) : String := s!"Knet={C.Knet}, Cproj={C.Cproj}"

/-- Check if a constants bundle matches the RS core. -/
noncomputable def coreMatchesRS (C : Constants) : Bool := (C.Knet = 1) && (C.Cproj = 2)

/-- Pretty print a universality report given a `Universality` record. -/
noncomputable def universalityReport (U : Universality) : String :=
  let h := coreSummary U.Hodge.C
  let r := coreSummary U.RH.C
  let n := coreSummary U.NS.C
  let g := coreSummary U.Goldbach.C
  let allMatch : Bool := coreMatchesRS U.Hodge.C && coreMatchesRS U.RH.C && coreMatchesRS U.NS.C && coreMatchesRS U.Goldbach.C
  let verdict := if allMatch then "OK: matches RS core (Knet=1, Cproj=2)" else "MISMATCH: does not match RS core"
  s!"CPM Universality Report\n  Hodge:    {h}\n  RH:       {r}\n  NS:       {n}\n  Goldbach: {g}\n  Verdict:  {verdict}"

/-- Boolean check for CI. -/
noncomputable def universalityOK (U : Universality) : Bool :=
  coreMatchesRS U.Hodge.C && coreMatchesRS U.RH.C && coreMatchesRS U.NS.C && coreMatchesRS U.Goldbach.C

/-- Default RS universality instance (all domains use RS core constants). -/
def rsUniversality : Universality := {
  Hodge    := RS_sig,
  RH       := RS_sig,
  NS       := RS_sig,
  Goldbach := RS_sig
}

/-- A default report that teams can `#eval` interactively. -/
noncomputable def defaultReport : String := universalityReport rsUniversality

end CPMReports
end URCAdapters
end IndisputableMonolith
