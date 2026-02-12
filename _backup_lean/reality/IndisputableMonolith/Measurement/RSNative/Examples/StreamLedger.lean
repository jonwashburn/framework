import IndisputableMonolith.Streams
import IndisputableMonolith.Measurement.RSNative

namespace IndisputableMonolith
namespace Measurement
namespace RSNative
namespace Examples
namespace StreamLedger

open IndisputableMonolith.Streams
open IndisputableMonolith.Measurement.RSNative

/-!
## Worked example: Stream → Ledger evidence → Trace → PathAction

This shows the end-to-end *plumbing*:
1) an observed Bool stream
2) a scaffold instrument adapter producing `LedgerState` evidence
3) a derived catalog observable on a trace (`pathAction`)

No SI calibration is involved.
-/

/-- A simple 8-bit window: first 4 bits are `true`, last 4 bits are `false`. -/
def window4On4Off : Pattern 8 :=
  fun i => decide (i.val < 4)

/-- Periodic stream repeating the 8-bit window. -/
def stream : Stream :=
  extendPeriodic8 window4On4Off

/-- Sample starting at tick 0. -/
def sample0 : Adapters.StreamToLedger.StreamSample8 :=
  { stream := stream, t0 := 0 }

-- Z-count and centered Z-charge are computable.
#eval Adapters.StreamToLedger.zWindow sample0
#eval Adapters.StreamToLedger.zCharge sample0

-- The rest of the pipeline is noncomputable (uses φ and ℝ operations), but typechecks end-to-end.
noncomputable def ledgerEvidence0 : Measurement IndisputableMonolith.Foundation.LedgerState :=
  Adapters.StreamToLedger.ledgerEvidence sample0

noncomputable def cost0 : Measurement Cost :=
  Catalog.Ledger.recognitionCost ledgerEvidence0.value

noncomputable def trace3 : Measurement (List IndisputableMonolith.Foundation.LedgerState) :=
  Adapters.StreamToLedger.traceOctaves 3 sample0

noncomputable def action3 : Measurement Cost :=
  Catalog.Ledger.pathAction trace3.value

end StreamLedger
end Examples
end RSNative
end Measurement
end IndisputableMonolith
