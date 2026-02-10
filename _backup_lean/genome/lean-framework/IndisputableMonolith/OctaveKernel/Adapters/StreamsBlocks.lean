import IndisputableMonolith.OctaveKernel.Basic
import IndisputableMonolith.Streams.Blocks

namespace IndisputableMonolith
namespace OctaveKernel
namespace Adapters

/-!
# OctaveKernel.Adapters.StreamsBlocks

This module “wires” the existing `Streams/Blocks.lean` results into the
`OctaveKernel` story without changing any definitions.

Claim hygiene:
- Everything here is either a *definition alias* or a *theorem re-export*.
- No new empirical claims, axioms, or hypotheses are introduced.
-/

namespace StreamsBlocks

abbrev Stream := PatternLayer.Stream
abbrev Pattern (n : Nat) := PatternLayer.Pattern n

abbrev Z_of_window {n : Nat} (w : Pattern n) : Nat :=
  PatternLayer.Z_of_window w

abbrev extendPeriodic8 (w : Pattern 8) : Stream :=
  PatternLayer.extendPeriodic8 w

abbrev subBlockSum8 (s : Stream) (j : Nat) : Nat :=
  MeasurementLayer.subBlockSum8 s j

abbrev blockSumAligned8 (k : Nat) (s : Stream) : Nat :=
  MeasurementLayer.blockSumAligned8 k s

abbrev observeAvg8 (k : Nat) (s : Stream) : Nat :=
  MeasurementLayer.observeAvg8 k s

theorem sumFirst8_extendPeriodic_eq_Z (w : Pattern 8) :
  PatternLayer.sumFirst 8 (extendPeriodic8 w) = Z_of_window w := by
  simpa [extendPeriodic8, Z_of_window] using PatternLayer.sumFirst8_extendPeriodic_eq_Z w

theorem subBlockSum8_periodic_eq_Z (w : Pattern 8) (j : Nat) :
  subBlockSum8 (extendPeriodic8 w) j = Z_of_window w := by
  simpa [subBlockSum8, extendPeriodic8, Z_of_window] using
    MeasurementLayer.subBlockSum8_periodic_eq_Z w j

theorem blockSumAligned8_periodic (w : Pattern 8) (k : Nat) :
  blockSumAligned8 k (extendPeriodic8 w) = k * Z_of_window w := by
  simpa [blockSumAligned8, extendPeriodic8, Z_of_window] using
    MeasurementLayer.blockSumAligned8_periodic w k

theorem observeAvg8_periodic_eq_Z {k : Nat} (hk : k ≠ 0) (w : Pattern 8) :
  observeAvg8 k (extendPeriodic8 w) = Z_of_window w := by
  simpa [observeAvg8, extendPeriodic8, Z_of_window] using
    MeasurementLayer.observeAvg8_periodic_eq_Z (k:=k) hk w

end StreamsBlocks

end Adapters
end OctaveKernel
end IndisputableMonolith
