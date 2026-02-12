import IndisputableMonolith.Measurement.RSNative.Core
import IndisputableMonolith.Measurement.RSNative.Catalog.Ledger
import IndisputableMonolith.Measurement.RSNative.Catalog.VoxelMeaning
import IndisputableMonolith.Measurement.RSNative.Catalog.Ethics
import IndisputableMonolith.Measurement.RSNative.Catalog.Qualia
import IndisputableMonolith.Measurement.RSNative.Alignment
import IndisputableMonolith.Measurement.RSNative.Adapters.StreamToLedger
import IndisputableMonolith.Measurement.RSNative.Adapters.VoxelToWToken

/-!
# RS-Native Measurement Framework (Entry Point)

Import this file to get:
- core measurement types (`Protocol`, `Window`, `Measurement`, `Observable`)
- tagged RS-native quantities (tick/voxel/coh/act/cost/skew/meaning/qualia/Z)
- initial catalog of RS-native observables for:
  - ledger/recognition (RecognitionCost, skew, Z)
  - voxel meaning (DFT spectrum)
  - ethics (MoralState skew + virtue selectors)
  - qualia (ULQ mode + qualia energy)
-/

namespace IndisputableMonolith
namespace Measurement
namespace RSNative

def status : String :=
  "✓ RSNative measurement core: Protocol/Window/Measurement/Observable\n" ++
  "✓ Tagged quantities: tick/voxel/coh/act/cost/skew/meaning/qualia/Z\n" ++
  "✓ Catalog: Ledger, VoxelMeaning, Ethics, Qualia\n" ++
  "✓ Cross-agent alignment seam: AlignmentProtocol / Alignment\n" ++
  "✓ Adapters (scaffold): Stream→Ledger, Voxel→WToken"

#eval status

end RSNative
end Measurement
end IndisputableMonolith
