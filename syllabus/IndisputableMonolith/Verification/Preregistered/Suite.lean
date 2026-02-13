import Mathlib

import IndisputableMonolith.Verification.Preregistered.AlphaInv.Test
import IndisputableMonolith.Verification.Preregistered.AlphaS.Test
import IndisputableMonolith.Verification.Preregistered.Hubble.Test
import IndisputableMonolith.Verification.Preregistered.Meaning.Test
import IndisputableMonolith.Verification.Exclusivity.NoAlternatives

/-!
# Preregistered Suite

This is the “do it now” version of the preregistration protocol:
- Predictions live in `Preregistered/*/Prediction.lean`
- Measurements live in `Preregistered/*/Measurement_*.lean`
- Tests live in `Preregistered/*/Test.lean`

We also include the model-independent exclusivity certificate as the formal
“alternatives require extra structure/parameters” component (within the modeled
class of frameworks).
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace Suite

open Verification.Exclusivity.NoAlternatives

def prereg_suite_ok : Prop :=
  (Preregistered.interval_contains Preregistered.AlphaInv.prediction
      Preregistered.AlphaInv.measurement_CODATA2022) ∧
    (Preregistered.within_sigma Preregistered.AlphaS.prediction
      Preregistered.AlphaS.measurement_PDG2022) ∧
    (abs (Preregistered.Hubble.H_early * Preregistered.Hubble.hubble_ratio.val - Preregistered.Hubble.H_late) /
        Preregistered.Hubble.H_late < 0.0005) ∧
    (Preregistered.within_sigma Preregistered.Hubble.omega_lambda
      Preregistered.Hubble.omega_lambda_measurement) ∧
    (∀ (F : Verification.Exclusivity.Framework.PhysicsFramework)
        (E : ExclusivityConstraintsV2 F),
        ∃ (φ : ℝ) (L : IndisputableMonolith.RecogSpec.Ledger)
          (RS : Verification.Exclusivity.Framework.PhysicsFramework),
          φ = IndisputableMonolith.Constants.phi ∧
            Verification.Exclusivity.Framework.FrameworkEquiv F RS)

theorem prereg_suite_ok_holds : prereg_suite_ok := by
  refine ⟨Preregistered.AlphaInv.passes_CODATA2022,
    Preregistered.AlphaS.passes_PDG2022_1sigma,
    Preregistered.Hubble.hubble_ratio_passes_rel_0p05pct,
    Preregistered.Hubble.omega_lambda_passes_1sigma,
    ?_⟩
  intro F E
  exact no_alternative_frameworks_derived (F := F) (E := E)

end Suite
end Preregistered
end Verification
end IndisputableMonolith
