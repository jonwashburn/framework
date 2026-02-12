import IndisputableMonolith.Chemistry.Quasicrystal

/-!
Demo: Quasicrystal Stability

#eval min energy at φ, peaks φ^k.
-/

namespace IndisputableMonolith
namespace Chemistry

#check quasicrystal_stable

#eval s!"Energy at φ = {tiling_energy Constants.phi} (min from J)"
#eval s!"Diffraction peaks at φ^k: k=0={diffraction_peak 0}, k=1={diffraction_peak 1}"

end Chemistry
end IndisputableMonolith
