import IndisputableMonolith.Foundation.Reference
import IndisputableMonolith.Foundation.WTokenReference
import IndisputableMonolith.Foundation.ReferenceWToken

/-!
# WToken Reference: Complete Import

This module provides a single import for all WToken reference functionality.

## The Algebra of Aboutness for WTokens

This module system formalizes how WTokens function as **semantic symbols** that
**refer** to concepts through **cost-minimizing compression**.

### Key Theorems

1. **Level-0 Universal Symbol**: Level-0 WTokens (J = 0) are universal compressors
   for any concept with positive cost.

   ```
   theorem level0_wtoken_is_universal_symbol :
       ∀ c : Concept, wtokenCost level0_wtoken < Jcost c.ratio
   ```

2. **Reference Triangle Inequality**: d'Alembert bounds chained reference.

   ```
   theorem wtoken_reference_triangle :
       R(w₁, w₃) ≤ 2R(w₁, w₂) + 2R(w₂, w₃) + 2R₁₂·R₂₃
   ```

3. **Self-Reference Zero**: A WToken has zero cost to reference itself.

   ```
   theorem wtoken_self_reference_zero :
       ∀ w, wtokenReference.cost w w = 0
   ```

4. **Geodesic Projection**: Project any ratio onto the optimal φ-level.

   ```
   def projectOntoPhiLattice (r : ℝ) (hr : 0 < r) : PhiLevel
   ```

### Theory Overview

The Recognition Science framework identifies 20 canonical WTokens as the
minimal-description-length (MDL) atoms for semantic encoding. These live on a
φ-lattice structure:

| Level | Ratio | Cost J(φ^k) | Interpretation |
|-------|-------|-------------|----------------|
| 0     | φ⁰=1  | 0           | Mathematical/pure |
| 1     | φ¹    | ~0.118      | Simple reference |
| 2     | φ²    | ~0.382      | Complex reference |
| 3     | φ³    | ~0.854      | Rich reference |

The cost of **referring** from WToken w to concept c is:
  R(w, c) = J(ratio_w / ratio_c)

A WToken is a **symbol** for a concept when:
1. It **means** the concept (minimizes reference cost)
2. It **compresses** the concept (J(w) < J(c))

Level-0 WTokens satisfy both conditions for all positive-cost concepts,
making them **universal semantic compressors**.

-/

namespace IndisputableMonolith.Foundation.WTokenReferenceAll

-- Re-export key definitions
open Reference
open WTokenReference
open ReferenceWToken

-- Check that key theorems are available
#check wtoken_reference_complete
#check level0_wtoken_is_universal_symbol
#check wtoken_self_reference_zero
#check algebra_of_aboutness_wtoken_summary

end IndisputableMonolith.Foundation.WTokenReferenceAll
