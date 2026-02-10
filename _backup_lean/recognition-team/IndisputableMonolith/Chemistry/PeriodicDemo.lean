import IndisputableMonolith.Chemistry.PeriodicBlocks

/-!
Demo: Periodic Table Blocks from φ-Packing

#eval shells n=1,2,3 ~ φ^{2,4,6} capacities.
-/

namespace IndisputableMonolith
namespace Chemistry

#check blocks_holds

#eval s!"Shell 1 energy = {shell_n 1} ~ φ^2 ≈2.618 E_coh"
#eval s!"Capacity n=1: {block_capacity 1} states"

end Chemistry
end IndisputableMonolith
