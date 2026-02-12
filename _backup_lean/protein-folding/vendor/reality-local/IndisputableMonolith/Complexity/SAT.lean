import IndisputableMonolith.Complexity.SAT.CNF
import IndisputableMonolith.Complexity.SAT.XOR
import IndisputableMonolith.Complexity.SAT.SmallBias
import IndisputableMonolith.Complexity.SAT.Isolation
import IndisputableMonolith.Complexity.SAT.Backprop
import IndisputableMonolith.Complexity.SAT.Completeness
import IndisputableMonolith.Complexity.SAT.PC
import IndisputableMonolith.Complexity.SAT.Runtime
import IndisputableMonolith.Complexity.SAT.GeoFamily

namespace IndisputableMonolith
namespace Complexity
namespace SAT

/-
Aggregator module for SAT program:
  Track A: Deterministic isolation via explicit XOR families
  Track B: Backpropagation completeness under isolation invariant
  Track C: Packaging with CA→TM bounds (composed elsewhere)
-/

end SAT
end Complexity
end IndisputableMonolith
