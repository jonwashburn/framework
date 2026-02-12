import Mathlib
import IndisputableMonolith.URCGenerators.UltimateCPMClosureCert
import IndisputableMonolith.URCGenerators.CPMClosureCert
import IndisputableMonolith.Verification.RecognitionReality

namespace IndisputableMonolith
namespace URCAdapters

/-!
# Ultimate + CPM Closure Report (URC Adapter)

Provides a simple `#eval`‑friendly string confirming that
both UltimateClosure (unique φ) and CPM closure verify.
-/

noncomputable def ultimate_cpm_closure_report : String :=
  -- Force use of both proofs so the adapter depends on the certificates.
  let _ : ∃ φ : ℝ, IndisputableMonolith.Verification.RecognitionReality.UltimateClosure φ :=
    ExistsUnique.exists
      (IndisputableMonolith.Verification.RecognitionReality.ultimate_closure_holds)
  let _ := IndisputableMonolith.URCGenerators.CPMClosureCert.verified_any {}
  "UltimateCPMClosure: OK"

@[simp] noncomputable def ultimate_cpm_closure_ok : String :=
  ultimate_cpm_closure_report

end URCAdapters
end IndisputableMonolith
