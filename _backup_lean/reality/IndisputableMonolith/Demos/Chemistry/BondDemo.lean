import IndisputableMonolith.Chemistry.BondAngles

/-!
Demo: Bond-Angle from φ-Min

#eval optimal angle ~109.47° (tetrahedral, from φ^{-1}).
-/

namespace IndisputableMonolith
namespace Chemistry

#check angle_bias

#eval s!"Optimal bond angle = {bond_angle 1 * 180 / Real.pi}° (tetrahedral ~109.47°)"

end Chemistry
end IndisputableMonolith
