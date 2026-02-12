import IndisputableMonolith.Physics.RunningCouplings

/-!
Demo: Running-Coupling Crossovers

#eval thresholds from rungs (m_c at rung=15), plateau φ^{-5} ~0.09, match QCD scales.
-/

namespace IndisputableMonolith
namespace Physics

#check crossover_holds

def c_quark : RSBridge.Fermion := RSBridge.Fermion.c  -- rung=15
def b_quark : RSBridge.Fermion := RSBridge.Fermion.b  -- rung=21

#eval s!"QCD crossover 3→4 at m_c threshold = {rung_threshold c_quark} ~ φ^{15}"
#eval s!"4→5 at m_b = {rung_threshold b_quark} ~ φ^{21} (Δr=6 → ×φ^6 ≈20.0)"
#eval s!"Plateau α ~ {eight_beat_plateau} (eight-beat fixed, β≈0)"
#eval s!"Empirical: PDG m_c≈1.27 GeV, RS pins via E_coh φ^r (falsifier: mismatch > bands)"

end Physics
end IndisputableMonolith
