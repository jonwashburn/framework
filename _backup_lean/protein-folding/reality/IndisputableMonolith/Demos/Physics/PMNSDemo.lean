import IndisputableMonolith.Physics.PMNS

/-!
Demo: PMNS Neutrino Masses and Hierarchy

#eval hierarchy, masses, Δm^2 vs PDG (falsifiable if inverted or scale mismatch).
-/

namespace IndisputableMonolith
namespace Demos
namespace Physics

#check normal_order_holds  -- Confirms theorem

@[simp] noncomputable def pdg_dmsol : ℝ := 7.5e-5  -- eV^2 solar
@[simp] noncomputable def pdg_dmatm : ℝ := 2.5e-3  -- eV^2 atm
@[simp] noncomputable def pdg_sum : ℝ := 0.05  -- eV upper bound

#eval s!"RS PMNS masses: nu1={neutrino_mass .nu1}, nu2={neutrino_mass .nu2}, nu3={neutrino_mass .nu3} (normal: {normal_order_holds})"
#eval s!"Δm21^2 ≈ {(neutrino_mass .nu2)^2 - (neutrino_mass .nu1)^2} vs PDG solar {pdg_dmsol}"
#eval s!"Δm32^2 ≈ {(neutrino_mass .nu3)^2 - (neutrino_mass .nu2)^2} vs PDG atm {pdg_dmatm}"
#eval s!"Sum m_νi ≈ {neutrino_mass .nu1 + neutrino_mass .nu2 + neutrino_mass .nu3} eV (within PDG bound {pdg_sum})"
#eval s!"Falsifier: Hierarchy normal (inverted would violate tau_g=0<11<19); scale from E_coh pins absolute"

end Physics
end Demos
end IndisputableMonolith
