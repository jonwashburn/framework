import IndisputableMonolith.Measurement.RSNative
import IndisputableMonolith.Measurement.RSNative.Calibration.SI
import IndisputableMonolith.OctaveKernel.VoxelMeaning

namespace IndisputableMonolith
namespace Measurement
namespace RSNative
namespace Examples
namespace VoxelEnergyToSI

open IndisputableMonolith.OctaveKernel
open IndisputableMonolith.Constants.RSNativeUnits

/-!
## Worked example: Voxel → RS energy measurement → optional SI reporting

This shows the calibration seam explicitly:
1) compute RS-native energy (`Coh`) from a `MeaningfulVoxel`
2) report the same measurement in SI Joules via an externally supplied `ExternalCalibration`
-/

/-- A toy voxel: one unit photon in phase 0, vacuum elsewhere. -/
def spikeVoxel : MeaningfulVoxel :=
  { photon := fun p => if p = 0 then Photon.unit else Photon.vacuum }

noncomputable def energyRS : Measurement Coh :=
  Catalog.VoxelMeaning.totalEnergy spikeVoxel

/-- Calibration is *external*; we keep it as a parameter in the example. -/
noncomputable def energyJ (cal : ExternalCalibration) : Measurement ℝ :=
  Calibration.SI.measure_to_joules cal energyRS

end VoxelEnergyToSI
end Examples
end RSNative
end Measurement
end IndisputableMonolith
