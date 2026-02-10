import IndisputableMonolith.BiophasePhysics.CrossSections
import IndisputableMonolith.BiophasePhysics.SNRCalculations
import IndisputableMonolith.BiophasePhysics.ChannelFeasibility

/-!
# BIOPHASE Physics Module Aggregator

Central import point for BIOPHASE physical calculations:
- Cross-sections (EM, gravitational, neutrino)
- SNR calculations
- Channel feasibility proofs

**Usage**:
```lean
import IndisputableMonolith.BiophasePhysics

open IndisputableMonolith.BiophasePhysics

#check biophase_cross_sections
#check biophase_snr_data
#check lemma_d_proven
```
-/

namespace IndisputableMonolith

namespace BiophasePhysics
-- Re-export main namespaces
end BiophasePhysics

end IndisputableMonolith

