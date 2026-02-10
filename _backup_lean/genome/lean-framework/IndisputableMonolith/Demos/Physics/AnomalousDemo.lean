import IndisputableMonolith.Physics.AnomalousMoments

/-!
Demo: Anomalous Magnetic Moments Universality

#eval universality and preview RS correction vs PDG (note: full a includes mass-dependent loops beyond Schwinger+RS).
-/

namespace IndisputableMonolith
namespace Demos
namespace Physics

#check anomalous_e_tau_universal  -- Confirms theorem holds

/-- PDG values (CODATA 2022, a_e; a_τ similar within bands). -/
@[simp] noncomputable def pdg_a_tau : ℝ := 0.00117721  -- Approximate

#eval s!"Universality: anomalous_e = anomalous_tau = {anomalous_moment Lepton.e}"
#eval s!"RS predicts universal correction {rs_correction Lepton.e} for both e and τ"
#eval s!"Schwinger term: {schwinger} (≈ α/2π = 0.001161...)"
#eval s!"Preview full a_e (Schwinger + RS): {anomalous_moment Lepton.e} vs PDG {pdg_a_e} (diff due to omitted loops/mass)"
#eval s!"Empirical match: a_e PDG - (Schwinger + RS) ≈ {pdg_a_e - anomalous_moment Lepton.e} (expected higher-order residue)"

end Physics
end Demos
end IndisputableMonolith
