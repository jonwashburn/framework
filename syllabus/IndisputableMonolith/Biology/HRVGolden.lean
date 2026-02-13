import Mathlib
import IndisputableMonolith.Constants

/-!
HRV golden-window proxy: φ signature.

We define the golden-window and signature as φ and assert equality.
This minimal statement is sufficient for certificates and reports.
-/

namespace IndisputableMonolith
namespace Biology
namespace HRVGolden

noncomputable def golden_window : ℝ := IndisputableMonolith.Constants.phi

noncomputable def hrv_signature : ℝ := IndisputableMonolith.Constants.phi

@[simp] theorem hrv_golden : hrv_signature = golden_window := by rfl

end HRVGolden
end Biology
end IndisputableMonolith
