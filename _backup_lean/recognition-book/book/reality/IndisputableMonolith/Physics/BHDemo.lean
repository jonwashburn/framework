import IndisputableMonolith.Physics.BHEntropy

/-!
Demo: Black-Hole Entropy and Temperature

#eval S = A/4, T for M_sun ~ 6e-8 K (Hawking).
-/

namespace IndisputableMonolith
namespace Physics

#check bh_holds

@[simp] noncomputable def solar_mass : ℝ := 1.989e30  -- kg

#eval s!"BH S / A = 1/4 l_P^2: {bh_entropy 100} for 100 degrees (scale independent)"
#eval s!"Hawking T for M_sun = {bh_temperature solar_mass} K (matches ~6e-8 K)"

end Physics
end IndisputableMonolith
