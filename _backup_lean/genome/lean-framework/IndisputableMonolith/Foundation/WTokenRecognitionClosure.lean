import IndisputableMonolith.Foundation.WTokenReference

/-!
# WToken Recognition Closure (argmin-based forcing)

This module upgrades the informal “recognition selects a WToken” story to a clean Lean theorem:

- `projectOntoPhiLattice` (already defined in `Foundation/WTokenReference`) chooses a φ-level
  that minimizes the RS mismatch cost \(J(r/\phi^k)\) over the finite set \(k∈\{0,1,2,3\}\).
- Because `referenceCost w c = J( ratio(w) / ratio(c) )` and `J` is symmetric under inversion,
  the same φ-level also minimizes the reference mismatch \(J(\phi^k / r)\).

We package this as a concrete witness for `recognitionAsReference` and as an explicit
`OptimalWToken` constructor.
-/

namespace IndisputableMonolith
namespace Foundation
namespace WTokenReference

open Cost

/-!
## A canonical “recognized” WToken (φ-level argmin)

The RS cost layer fixes the φ-level by argmin. The mode family and τ-variant are orthogonal
to this cost (they are handled by the DFT/basis-class layer elsewhere), so we choose a
canonical representative for them here.
-/

noncomputable def recognizePhiLevel (c : Concept) : ReferenceWToken.PhiLevel :=
  projectOntoPhiLattice c.ratio c.ratio_pos

noncomputable def recognizeWToken (c : Concept) : ReferenceWToken.WTokenSpec :=
  { mode := ReferenceWToken.ModeFamilyId.mode1_7
    phi_level := recognizePhiLevel c
    tau_offset := ReferenceWToken.TauOffset.tau0
    tau_valid := by decide }

/-!
## Reference-cost normalization lemma

`wtokenConceptReference.cost w c = J( ratio(w) / ratio(c) )`.
For argmin comparisons, it is convenient to flip the ratio using symmetry `J(x)=J(x⁻¹)`.
-/

lemma referenceCost_eq_J_ratio_div (w : ReferenceWToken.WTokenSpec) (c : Concept) :
    referenceCost w c = Jcost (wtokenRatio w / c.ratio) := by
  rfl

lemma referenceCost_eq_J_ratio_div_symm (w : ReferenceWToken.WTokenSpec) (c : Concept) :
    referenceCost w c = Jcost (c.ratio / wtokenRatio w) := by
  -- Use J symmetry: J(x) = J(x⁻¹)
  have hx : 0 < (wtokenRatio w / c.ratio) := div_pos (wtokenRatio_pos w) c.ratio_pos
  -- `(wtokenRatio/c.ratio)⁻¹ = c.ratio/wtokenRatio`
  -- `Jcost_symm` rewrites `J(x)` as `J(x⁻¹)` for positive `x`.
  -- Here `x = wtokenRatio w / c.ratio`, so `x⁻¹ = c.ratio / wtokenRatio w`.
  have : Jcost (wtokenRatio w / c.ratio) = Jcost (c.ratio / wtokenRatio w) := by
    simpa [inv_div] using (Jcost_symm hx)
  simpa [referenceCost_eq_J_ratio_div, this]

lemma referenceCost_eq_phiLevelRefCost (w : ReferenceWToken.WTokenSpec) (c : Concept) :
    referenceCost w c = phiLevelRefCost c.ratio w.phi_level := by
  -- `referenceCost w c = J( ratio(w) / ratio(c) ) = J( ratio(c) / ratio(w) )`
  -- and `ratio(w) = phi^(phiLevelExponent w.phi_level)`.
  have hsymm : referenceCost w c = Jcost (c.ratio / wtokenRatio w) :=
    referenceCost_eq_J_ratio_div_symm w c
  -- Expand `phiLevelRefCost` and `wtokenRatio`.
  simpa [phiLevelRefCost, wtokenRatio] using hsymm

/-!
## Recognition (φ-level) is an argmin
-/

theorem recognizeWToken_optimal (c : Concept) :
    ∀ w' : ReferenceWToken.WTokenSpec, referenceCost (recognizeWToken c) c ≤ referenceCost w' c := by
  intro w'
  -- Reduce to the φ-level argmin statement proved in `WTokenReference`.
  have hproj :=
    projection_minimizes_reference (r := c.ratio) (hr := c.ratio_pos) (level := w'.phi_level)
  -- Rewrite both sides as `phiLevelRefCost` and then apply the minimizer inequality.
  have hL : referenceCost (recognizeWToken c) c =
      phiLevelRefCost c.ratio (recognizeWToken c).phi_level := by
    simpa using referenceCost_eq_phiLevelRefCost (w := recognizeWToken c) (c := c)
  have hR : referenceCost w' c = phiLevelRefCost c.ratio w'.phi_level := by
    simpa using referenceCost_eq_phiLevelRefCost (w := w') (c := c)
  -- `recognizeWToken`'s φ-level is exactly the lattice projection.
  have hphi : (recognizeWToken c).phi_level = projectOntoPhiLattice c.ratio c.ratio_pos := by
    rfl
  -- Finish.
  -- `hproj` already has the form `phiLevelRefCost c.ratio proj ≤ phiLevelRefCost c.ratio w'.phi_level`.
  -- We just transport it across `hL`, `hR`, and `hphi`.
  simpa [hL, hR, hphi, recognizePhiLevel, phiLevelRefCost] using hproj

theorem recognitionAsReference_holds (c : Concept) :
    recognitionAsReference c := by
  refine ⟨recognizeWToken c, Or.inr ?_⟩
  intro w'
  exact recognizeWToken_optimal c w'

/-!
## Existence of an optimal WToken (explicit constructor)
-/

noncomputable def optimalWToken (c : Concept) : OptimalWToken c :=
  { wtoken := recognizeWToken c
    is_optimal := recognizeWToken_optimal c }

end WTokenReference
end Foundation
end IndisputableMonolith
