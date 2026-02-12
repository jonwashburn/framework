import IndisputableMonolith.BiophaseCore.Constants
import IndisputableMonolith.BiophaseCore.Specification
import IndisputableMonolith.BiophaseCore.EightBeatBands

/-!
# BIOPHASE Core Module Aggregator

Central import point for BIOPHASE core specification:
- Physical constants (φ⁻⁵ eV, 13.8 μm, 724 cm⁻¹)
- Full specification with eight-beat bands
- Band structure and acceptance predicates

**Usage**:
```lean
import IndisputableMonolith.BiophaseCore

open IndisputableMonolith.BiophaseCore

#check E_biophase
#check StandardBiophaseSpec
#check StandardEightBeatBands
```
-/

namespace IndisputableMonolith

namespace BiophaseCore
-- Re-export main namespaces
end BiophaseCore

end IndisputableMonolith

