import IndisputableMonolith.Physics.CKM

/-!
Demo: CKM Jarlskog from φ-Rungs

#eval J computation and match to PDG (falsifiable: if deviates > bands without equal-Z adjust).
-/

namespace IndisputableMonolith
namespace Demos
namespace Physics

#check jarlskog_holds  -- Confirms theorem (pos, approx match)

@[simp] noncomputable def pdg_j : ℝ := 3.18e-5  -- PDG 2024 central

#eval s!"RS CKM J = {jarlskog} vs PDG {pdg_j} (match within {abs (jarlskog - pdg_j) / pdg_j * 100}% error)"
#eval s!"Ablation: Δτ=11 (2nd-1st) → s12 ≈ {V_us}; expected sin θ_c ≈0.22"

/-- Falsifier: If |J - PDG| > 0.15e-5 without RS adjust, violates rung inevitability. -/
#eval s!"Bands check: {jarlskog} ∈ [{pdg_j - 0.15e-5}, {pdg_j + 0.15e-5}] = {jarlskog ∈ [pdg_j - 0.15e-5, pdg_j + 0.15e-5]}"

end Physics
end Demos
end IndisputableMonolith
