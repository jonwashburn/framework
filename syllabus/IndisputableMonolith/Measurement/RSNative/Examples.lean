import IndisputableMonolith.Measurement.RSNative.Examples.StreamLedger
import IndisputableMonolith.Measurement.RSNative.Examples.VoxelEnergyToSI
import IndisputableMonolith.Measurement.RSNative.Examples.AlignmentScaffold

/-!
# RS-Native Measurement — Worked Examples

Build:
- `lake build IndisputableMonolith.Measurement.RSNative.Examples`

These examples are intentionally small and focus on end-to-end wiring:
- observed data → RS evidence → RS-native observables
- optional calibration seam (RS → SI)
- alignment seam (cross-agent comparison protocol)
-/

namespace IndisputableMonolith.Measurement.RSNative.Examples

def status : String :=
  "✓ Worked examples: Stream→Ledger→PathAction\n" ++
  "✓ Worked examples: Voxel→Energy→(optional) SI Joules\n" ++
  "✓ Worked examples: Alignment seam (map + protocol)"

#eval status

end IndisputableMonolith.Measurement.RSNative.Examples
