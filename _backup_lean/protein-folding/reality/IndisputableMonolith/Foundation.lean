import IndisputableMonolith.Foundation.RecognitionOperator
import IndisputableMonolith.Foundation.HamiltonianEmergence

/-!
# Foundation Module Aggregator

This module aggregates foundational definitions establishing the Recognition Operator R̂
as the fundamental object of Recognition Science, with the energy Hamiltonian Ĥ emerging
as a small-deviation approximation.

**Structure**:
- `RecognitionOperator`: R̂ definition, minimizes J-cost not energy
- `HamiltonianEmergence`: Proof that Ĥ emerges from R̂ in small-ε limit

**Usage**:
```lean
import IndisputableMonolith.Foundation

open IndisputableMonolith.Foundation

-- Access definitions
#check RecognitionOperator
#check THEOREM_recognition_operator_fundamental
#check THEOREM_hamiltonian_derived_not_fundamental
```
-/

namespace IndisputableMonolith

namespace Foundation
end Foundation

end IndisputableMonolith
