import IndisputableMonolith.Chemistry.SuperconductingTc

/-!
Demo: Superconducting Tc Scaling

#eval Tc decrease with Δr gap.
-/

namespace IndisputableMonolith
namespace Chemistry

#check tc_scaling

#eval s!"Tc for Δr=1: {tc_phonon 1}, Δr=2: {tc_phonon 2} (decrease from ladder)"

end Chemistry
end IndisputableMonolith
