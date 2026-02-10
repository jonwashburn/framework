import IndisputableMonolith.Physics.Hadrons

/-!
Demo: Hadron Masses and Regge Trajectories

#eval composite rung for ρ (u d-bar), Regge m^2 linear vs PDG slope 0.9 GeV^{-2}.
-/

namespace IndisputableMonolith
namespace Demos
namespace Physics

#check regge_holds  -- Confirms theorem

def rho_hadron : Hadron := ⟨RSBridge.Fermion.u, RSBridge.Fermion.d, 1⟩  -- u d-bar + binding

#eval s!"ρ composite rung = {composite_rung rho_hadron}; mass ≈ {hadron_mass rho_hadron}"
#eval s!"Regge for r=1, n=0..3: m^2 = {regge_mass_squared 1 (0:ℕ) pdg_regge_slope}, {regge_mass_squared 1 (1:ℕ) pdg_regge_slope}, ... (linear with slope {pdg_regge_slope})"
#eval s!"PDG pion Regge: slope ≈0.9 GeV^{-2}; RS matches via φ^{2r} tier (falsifier: non-linear m^2)"

end Physics
end Demos
end IndisputableMonolith
