import IndisputableMonolith.Measurement.RSNative.Core
import IndisputableMonolith.ULQ.Core
import IndisputableMonolith.ULQ.Dynamics

/-!
# RS-Native Measurement Catalog: Qualia (ULQ)

ULQ already defines RS-native qualia primitives:
- mode (from DFT structure)
- intensity (φ-level)
- valence (bounded [-1,1])
- temporal quality (τ-offset in Fin 8)

This catalog provides small, protocol-carrying observables for those primitives.
-/

namespace IndisputableMonolith
namespace Measurement
namespace RSNative
namespace Catalog
namespace Qualia

open IndisputableMonolith
open ULQ

@[simp] def asQualia (x : ℝ) : RSNative.Qualia := ⟨x⟩

def protocol_qualiaModeOfWToken : Protocol :=
{ name := "qualia.mode_of_wtoken"
, summary := "Qualia mode derived from a WToken’s non-DC dominant DFT mode (ULQ.Core)."
, status := .derived
, assumptions := ["Token is neutral (DC excluded) as in ULQ/ULL constraints."]
, falsifiers := []
}

def protocol_qualiaEnergy : Protocol :=
{ name := "qualia.energy"
, summary := "QualiaEnergy(q) := φ^(level) * (1 + |valence|) (ULQ.Dynamics)."
, status := .derived
, assumptions := []
, falsifiers := []
}

noncomputable def qualiaModeOfWToken : Observable LightLanguage.WToken ULQ.QualiaMode :=
  fun w =>
  { value := ULQ.qualiaModeOfWToken w
  , window := none
  , protocol := protocol_qualiaModeOfWToken
  }

noncomputable def qualiaEnergy : Observable ULQ.QualiaSpace RSNative.Qualia :=
  fun q =>
  { value := asQualia (ULQ.Dynamics.qualiaEnergy q)
  , window := none
  , protocol := protocol_qualiaEnergy
  }

end Qualia
end Catalog
end RSNative
end Measurement
end IndisputableMonolith


