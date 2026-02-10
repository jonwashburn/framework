import IndisputableMonolith.Measurement.RSNative.Core
import IndisputableMonolith.OctaveKernel.VoxelMeaning

/-!
# RS-Native Measurement Catalog: Voxel Meaning

Observables on `OctaveKernel.MeaningfulVoxel` (DFT-based meaning primitives).
-/

namespace IndisputableMonolith
namespace Measurement
namespace RSNative
namespace Catalog
namespace VoxelMeaning

open IndisputableMonolith.OctaveKernel

@[simp] def asCoh (x : ℝ) : RSNative.Coh := ⟨x⟩

def protocol_totalEnergy : Protocol :=
{ name := "voxel.total_energy"
, summary := "Total voxel energy: Σ_p amplitude(p)^2 (RS-native energy units)."
, status := .derived
, assumptions := []
, falsifiers := []
}

def protocol_modeEnergy : Protocol :=
{ name := "voxel.mode_energy"
, summary := "Per-mode energy: (modeAmplitude k)^2 for k∈Fin 8 (DFT spectrum)."
, status := .derived
, assumptions := []
, falsifiers := []
}

noncomputable def totalEnergy : Observable MeaningfulVoxel RSNative.Coh :=
  fun v =>
  { value := asCoh v.totalEnergy
  , window := none
  , protocol := protocol_totalEnergy
  }

noncomputable def modeEnergy (k : Fin 8) : Observable MeaningfulVoxel RSNative.Coh :=
  fun v =>
  { value := asCoh ((v.modeAmplitude k) ^ 2)
  , window := none
  , protocol := protocol_modeEnergy
  , notes := ["Interpretation: squared DFT-mode amplitude."]
  }

noncomputable def spectrum : Observable MeaningfulVoxel (Fin 8 → RSNative.Coh) :=
  fun v =>
  { value := fun k => asCoh ((v.modeAmplitude k) ^ 2)
  , window := none
  , protocol := protocol_modeEnergy
  }

end VoxelMeaning
end Catalog
end RSNative
end Measurement
end IndisputableMonolith


