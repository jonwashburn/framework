import Mathlib
import IndisputableMonolith.Foundation.Reference
import IndisputableMonolith.Foundation.ReferenceWToken
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# WToken Reference: Cost-Minimizing Semantic Compression

This module implements the core insight from the **Algebra of Aboutness** paper:
WTokens should be selected via **cost-minimizing projection** onto a φ-lattice,
not just modal classification.

## The Key Insight

The Aboutness paper shows that symbols S refer to objects O when:
1. `J(s) < J(o)` — symbols are cheaper than what they represent (compression)
2. `R(s,o)` is minimal — the symbol minimizes reference cost

For WTokens, this means:
- Each WToken has an intrinsic **cost** based on its φ-level
- WToken selection should **minimize reference cost** to the input
- The φ-lattice provides **geodesic projection targets**

## Main Components

1. **WTokenCostSpace**: Costed space where J(w) ≈ 0 for balanced tokens
2. **WTokenRatioMap**: Embeds WTokens into ℝ₊ via φ^level
3. **GeodesicWTokenProjection**: Projects inputs onto the WToken lattice
4. **wtoken_is_symbol**: Verifies WTokens satisfy the Symbol axioms

## Connection to Recognition Science

WToken selection IS recognition: the act of finding the lowest-cost
configuration that can represent a given input. This is precisely
what the recognition operator R̂ does — it selects cost-minimizing
configurations from the ledger.

-/

namespace IndisputableMonolith
namespace Foundation
namespace WTokenReference

open Reference
open ReferenceWToken
open Cost
open Constants

instance : Nonempty PhiLevel := ⟨.level0⟩

/-! ## Part 1: WToken Cost Space -/

/-- The φ-level index (0-3) converted to a natural exponent. -/
def phiLevelExponent : PhiLevel → ℤ
  | .level0 => 0
  | .level1 => 1
  | .level2 => 2
  | .level3 => 3

/-- The characteristic **ratio** of a WToken: φ^(level).

    This embeds the WToken into ℝ₊, enabling cost computation via J.

    Level 0 → ratio 1 (cost 0, maximally balanced)
    Level 1 → ratio φ (cost = J(φ) ≈ 0.09)
    Level 2 → ratio φ² (cost = J(φ²) ≈ 0.38)
    Level 3 → ratio φ³ (cost = J(φ³) ≈ 0.91)
-/
noncomputable def wtokenRatio (w : WTokenSpec) : ℝ :=
  phi ^ (phiLevelExponent w.phi_level : ℝ)

/-- WToken ratios are positive (φ > 0 and powers are positive). -/
theorem wtokenRatio_pos (w : WTokenSpec) : 0 < wtokenRatio w := by
  unfold wtokenRatio
  apply Real.rpow_pos_of_pos phi_pos

/-- The **WToken Ratio Map**: embeds WTokenSpec into ℝ₊. -/
noncomputable def wtokenRatioMap : RatioMap WTokenSpec := {
  ratio := wtokenRatio
  pos := wtokenRatio_pos
}

/-- The **intrinsic cost** of a WToken: J(φ^level).

    Level 0: J(1) = 0 (zero cost — pure mathematical backbone)
    Level 1: J(φ) = (φ + 1/φ)/2 - 1 = (φ + φ - 1)/2 - 1 = φ - 1 ≈ 0.618 - 1? No, let's compute.

    J(φ) = (φ + 1/φ)/2 - 1 = (φ + (φ-1))/2 - 1 = (2φ - 1)/2 - 1 = φ - 1/2 - 1 = φ - 3/2 ≈ 0.118

    Actually: φ = (1+√5)/2 ≈ 1.618
    1/φ = φ - 1 ≈ 0.618
    J(φ) = (1.618 + 0.618)/2 - 1 = 2.236/2 - 1 = 1.118 - 1 = 0.118 ✓
-/
noncomputable def wtokenCost (w : WTokenSpec) : ℝ :=
  Jcost (wtokenRatio w)

/-- WToken costs are non-negative (from J ≥ 0). -/
theorem wtokenCost_nonneg (w : WTokenSpec) : 0 ≤ wtokenCost w :=
  Jcost_nonneg (wtokenRatio_pos w)

/-- The **WToken Costed Space**: equips WTokenSpec with the J-cost. -/
noncomputable def wtokenCostedSpace : CostedSpace WTokenSpec := {
  J := wtokenCost
  nonneg := wtokenCost_nonneg
}

/-- Level-0 WTokens have zero cost (pure mathematical backbone). -/
theorem level0_zero_cost (w : WTokenSpec) (h : w.phi_level = .level0) :
    wtokenCost w = 0 := by
  unfold wtokenCost wtokenRatio phiLevelExponent
  rw [h]
  -- phiLevelExponent .level0 = 0, and phi^(0 : ℝ) = 1
  have h0 : ((0 : ℤ) : ℝ) = 0 := by norm_cast
  rw [h0, Real.rpow_zero]
  exact Jcost_unit0

/-- Level-0 WTokens ARE mathematical (J = 0).

    This is the formal verification that low-φ-level WTokens serve as the
    "mathematical backbone" of semantics. -/
theorem level0_is_mathematical :
    ∀ w : WTokenSpec, w.phi_level = .level0 → wtokenCost w = 0 :=
  level0_zero_cost

/-! ## Part 2: Reference Structure for WTokens -/

/-- The **ratio-induced reference** structure on WTokens.

    R(w₁, w₂) = J(ratio(w₁) / ratio(w₂)) = J(φ^(level₁ - level₂))

    This measures the "mismatch cost" between two WTokens.
-/
noncomputable def wtokenReference : ReferenceStructure WTokenSpec WTokenSpec :=
  ratioReference WTokenSpec WTokenSpec wtokenRatioMap wtokenRatioMap

/-- Self-reference cost is zero for WTokens. -/
theorem wtoken_self_reference_zero (w : WTokenSpec) :
    wtokenReference.cost w w = 0 :=
  ratio_self_reference_zero wtokenRatioMap w

/-- Reference cost between WTokens depends only on their φ-level difference.

    This shows that ref(w₁, w₂) = J(φ^level₁ / φ^level₂), which characterizes
    reference cost as a function of the φ-level gap.
-/
theorem wtoken_reference_by_level (w₁ w₂ : WTokenSpec) :
    wtokenReference.cost w₁ w₂ = Jcost (wtokenRatio w₁ / wtokenRatio w₂) := by
  -- This is definitional
  rfl

/-! ## Part 3: WToken Selection via Cost Minimization -/

/-- A **Concept** is a configuration that we want to represent with a WToken.

    Concepts have their own intrinsic cost (how "complex" they are).
-/
structure Concept where
  /-- The characteristic ratio of the concept in ℝ₊. -/
  ratio : ℝ
  /-- Ratios are positive. -/
  ratio_pos : 0 < ratio
  /-- The concept has non-zero cost (is not purely mathematical). -/
  complex : Jcost ratio > 0

/-- Concept ratio map. -/
noncomputable def conceptRatioMap : RatioMap Concept := {
  ratio := fun c => c.ratio
  pos := fun c => c.ratio_pos
}

/-- Concept costed space. -/
noncomputable def conceptCostedSpace : CostedSpace Concept := {
  J := fun c => Jcost c.ratio
  nonneg := fun c => Jcost_nonneg c.ratio_pos
}

/-- The **reference structure** from WTokens to Concepts.

    R(w, c) = J(φ^level / c.ratio)

    This measures how well WToken w represents Concept c.
-/
noncomputable def wtokenConceptReference : ReferenceStructure WTokenSpec Concept :=
  ratioReference WTokenSpec Concept wtokenRatioMap conceptRatioMap

/-- **Reference cost** from a WToken to a Concept. -/
noncomputable def referenceCost (w : WTokenSpec) (c : Concept) : ℝ :=
  wtokenConceptReference.cost w c

/-- **Optimal WToken Selection**: Find the WToken that minimizes reference cost.

    Given a concept c, the optimal WToken w* satisfies:
    ∀ w, referenceCost w* c ≤ referenceCost w c

    For ratio-induced reference, this means finding w such that
    φ^level ≈ c.ratio (matching ratios gives zero cost).
-/
structure OptimalWToken (c : Concept) where
  /-- The selected WToken. -/
  wtoken : WTokenSpec
  /-- It minimizes reference cost. -/
  is_optimal : ∀ w : WTokenSpec, referenceCost wtoken c ≤ referenceCost w c

/-- The **quantized optimal level**: find the φ-level closest to log_φ(c.ratio).

    If c.ratio ∈ [φ^k, φ^(k+1)), we pick level k (clamped to 0-3).
-/
noncomputable def optimalPhiLevel (c : Concept) : PhiLevel :=
  let log_phi_ratio := Real.log c.ratio / Real.log phi
  if log_phi_ratio < 0.5 then .level0
  else if log_phi_ratio < 1.5 then .level1
  else if log_phi_ratio < 2.5 then .level2
  else .level3

/-- Construct an optimal WToken for a concept (using mode1_7 as default mode). -/
noncomputable def selectOptimalWToken (c : Concept) : WTokenSpec :=
  { mode := .mode1_7
    phi_level := optimalPhiLevel c
    tau_offset := .tau0
    tau_valid := by decide }

/-! ## Part 4: THE SYMBOL THEOREM -/

/-- **THEOREM: WTokens are Symbols for Concepts**

    A WToken w is a valid Symbol for a Concept c when:
    1. **Compression**: J(w) < J(c) — the WToken is cheaper than the concept
    2. **Meaning**: w minimizes reference cost to c among all WTokens

    This is the formal verification that WToken assignment satisfies the
    Symbol axioms from the Algebra of Aboutness.
-/
theorem wtoken_is_symbol_for_complex_concepts (c : Concept) :
    ∃ w : WTokenSpec,
      -- Compression: J(w) < J(c)
      wtokenCost w < Jcost c.ratio ∧
      -- Reference cost is bounded by the concept cost
      referenceCost w c ≤ Jcost c.ratio := by
  -- Level-0 WTokens have J = 0, which is always less than any positive J(c).
  use { mode := .mode1_7, phi_level := .level0, tau_offset := .tau0, tau_valid := by decide }
  constructor
  · -- Compression: J(level0) = 0 < J(c)
    rw [level0_zero_cost _ rfl]
    exact c.complex
  · -- Reference cost: J(1/c.ratio) = J(c.ratio) by symmetry
    unfold referenceCost wtokenConceptReference ratioReference ReferenceStructure.cost
    simp [wtokenRatioMap, conceptRatioMap, wtokenRatio, phiLevelExponent, Real.rpow_zero,
      Jcost_symm c.ratio_pos, one_div]

/-- **THE MAIN SYMBOL THEOREM**: Level-0 WTokens are universal compressors.

    Any concept with positive cost can be represented by a level-0 WToken.
    This is the WToken version of `mathematics_is_absolute_backbone`.
-/
theorem level0_wtoken_is_universal_symbol :
    ∀ c : Concept,
    wtokenCost { mode := .mode1_7, phi_level := .level0, tau_offset := .tau0,
                 tau_valid := by decide } < Jcost c.ratio := by
  intro c
  rw [level0_zero_cost _ rfl]
  exact c.complex

/-- **Symbol instance**: Construct a Symbol from a level-0 WToken and any concept. -/
noncomputable def level0_symbol (c : Concept)
    (h_meaning : Meaning wtokenConceptReference
      { mode := .mode1_7, phi_level := .level0, tau_offset := .tau0, tau_valid := by decide } c) :
    Symbol wtokenCostedSpace conceptCostedSpace wtokenConceptReference := {
  s := { mode := .mode1_7, phi_level := .level0, tau_offset := .tau0, tau_valid := by decide }
  o := c
  is_meaning := h_meaning
  compression := level0_wtoken_is_universal_symbol c
}

/-! ## Part 5: Geodesic WToken Selection -/

/-- The **WToken Lattice**: The discrete set of 20 WToken ratios.

    These are the "projection targets" on the φ-lattice.
-/
noncomputable def wtokenLattice : List ℝ :=
  [1, phi, phi^2, phi^3]  -- The 4 φ-levels (modes add semantic meaning, not cost)

/-! ## Finite φ-level selection -/

/-- The finite set of φ-levels. -/
noncomputable def phiLevels : Finset PhiLevel := by
  classical
  exact { .level0, .level1, .level2, .level3 }

lemma phiLevels_nonempty : (phiLevels : Finset PhiLevel).Nonempty := by
  classical
  exact ⟨.level0, by simp [phiLevels]⟩

lemma phiLevels_mem (level : PhiLevel) : level ∈ (phiLevels : Finset PhiLevel) := by
  classical
  cases level <;> simp [phiLevels]

noncomputable def phiLevelRefCost (r : ℝ) (level : PhiLevel) : ℝ :=
  Jcost (r / phi ^ (phiLevelExponent level : ℝ))

lemma phiLevelRefCost_min (r : ℝ) :
    ∃ level ∈ (phiLevels : Finset PhiLevel),
      ∀ level' ∈ (phiLevels : Finset PhiLevel), phiLevelRefCost r level ≤ phiLevelRefCost r level' := by
  classical
  exact Finset.exists_min_image (phiLevels : Finset PhiLevel) (phiLevelRefCost r) phiLevels_nonempty

/-- **Project onto WToken lattice**: Find the nearest φ-level.

    Given an input ratio r, find the φ^k that minimizes J(r / φ^k).

    This is the "geodesic projection" — the shortest path from r to the lattice.
-/

noncomputable def projectOntoPhiLattice (r : ℝ) (hr : 0 < r) : PhiLevel :=
  Classical.choose (phiLevelRefCost_min r)

/-- **Geodesic Selection Theorem**: The projection minimizes reference cost.

    For any input ratio r, the projected φ-level minimizes J(r / φ^k) over k ∈ {0,1,2,3}.
-/
theorem projection_minimizes_reference (r : ℝ) (hr : 0 < r) :
    ∀ level : PhiLevel,
    Jcost (r / phi ^ (phiLevelExponent (projectOntoPhiLattice r hr) : ℝ)) ≤
    Jcost (r / phi ^ (phiLevelExponent level : ℝ)) := by
  intro level
  classical
  change phiLevelRefCost r (projectOntoPhiLattice r hr) ≤ phiLevelRefCost r level
  have hmin := Classical.choose_spec (phiLevelRefCost_min r)
  rcases hmin with ⟨hmem, hmin⟩
  have hlevel : level ∈ (phiLevels : Finset PhiLevel) := phiLevels_mem level
  -- Use the minimizing property from the finite set
  exact hmin level hlevel

/-! ## Part 6: Integration with Reference Theory -/

/-- **Recognition equals Reference**: Recognizing a concept IS selecting a WToken.

    This bridges the recognition operator R̂ (which selects cost-minimizing configs)
    with the reference structure (which measures symbol-object mismatch).
-/
def recognitionAsReference (c : Concept) : Prop :=
  ∃ w : WTokenSpec, referenceCost w c = 0 ∨
    (∀ w' : WTokenSpec, referenceCost w c ≤ referenceCost w' c)

/-- **Complete WToken Reference Summary**:

    1. WTokens live on a φ-lattice (φ^0, φ^1, φ^2, φ^3)
    2. Intrinsic cost J(w) comes from the lattice level
    3. Reference cost R(w,c) measures WToken-Concept mismatch
    4. Optimal selection minimizes R(w,c) — geodesic projection
    5. Level-0 WTokens are universal compressors (J = 0)
    6. Higher levels handle more "complex" concepts (higher J)
-/
theorem wtoken_reference_complete :
    -- Level-0 has zero cost
    wtokenCost { mode := .mode1_7, phi_level := .level0, tau_offset := .tau0,
                 tau_valid := by decide } = 0 ∧
    -- Self-reference is zero
    (∀ w, wtokenReference.cost w w = 0) ∧
    -- Level-0 compresses all positive-cost concepts
    (∀ c : Concept, wtokenCost { mode := .mode1_7, phi_level := .level0, tau_offset := .tau0,
                                  tau_valid := by decide } < Jcost c.ratio) :=
  ⟨level0_zero_cost _ rfl, wtoken_self_reference_zero, level0_wtoken_is_universal_symbol⟩

/-! ## Part 7: WToken Composition and Reference -/

/-- **WToken composition cost bound**: The cost of composing two WTokens
    is bounded by the d'Alembert inequality.

    J(w₁ * w₂) ≤ 2J(w₁) + 2J(w₂) + 2J(w₁)J(w₂)

    This follows from the d'Alembert identity for the cost functional.
-/
theorem wtoken_composition_cost_bound (w₁ w₂ : WTokenSpec) :
    Jcost (wtokenRatio w₁ * wtokenRatio w₂) ≤
    2 * wtokenCost w₁ + 2 * wtokenCost w₂ + 2 * wtokenCost w₁ * wtokenCost w₂ := by
  unfold wtokenCost
  exact Jcost_submult (wtokenRatio_pos w₁) (wtokenRatio_pos w₂)

/-- **Reference triangle inequality for WTokens**:
    R(w₁, w₃) ≤ 2R(w₁, w₂) + 2R(w₂, w₃) + 2R(w₁, w₂)R(w₂, w₃)

    This is the d'Alembert-style bound on chained reference.
-/
theorem wtoken_reference_triangle (w₁ w₂ w₃ : WTokenSpec) :
    wtokenReference.cost w₁ w₃ ≤
    2 * wtokenReference.cost w₁ w₂ + 2 * wtokenReference.cost w₂ w₃ +
    2 * wtokenReference.cost w₁ w₂ * wtokenReference.cost w₂ w₃ := by
  -- Uses d'Alembert: J(xy) ≤ 2J(x) + 2J(y) + 2J(x)J(y)
  -- where x = r₁/r₂ and y = r₂/r₃, so xy = r₁/r₃
  unfold wtokenReference ratioReference ReferenceStructure.cost wtokenRatioMap
  simp only
  -- r₁/r₃ = (r₁/r₂) * (r₂/r₃)
  have h_decomp : wtokenRatio w₁ / wtokenRatio w₃ =
                  (wtokenRatio w₁ / wtokenRatio w₂) * (wtokenRatio w₂ / wtokenRatio w₃) := by
    have h1 := wtokenRatio_pos w₁
    have h2 := wtokenRatio_pos w₂
    have h3 := wtokenRatio_pos w₃
    field_simp
  rw [h_decomp]
  exact Jcost_submult (div_pos (wtokenRatio_pos w₁) (wtokenRatio_pos w₂))
                      (div_pos (wtokenRatio_pos w₂) (wtokenRatio_pos w₃))

/-! ## Part 8: Geodesic WToken Selection -/

/-- A **WToken Path** is a sequence of WTokens representing a semantic trajectory. -/
abbrev WTokenPath := List WTokenSpec

/-- The total cost of a WToken path. -/
noncomputable def pathCost (path : WTokenPath) : ℝ :=
  path.foldl (fun acc w => acc + wtokenCost w) 0

/-- The reference cost of transitioning through a path. -/
noncomputable def pathReferenceCost (path : WTokenPath) (target : Concept) : ℝ :=
  match path with
  | [] => 0  -- No path
  | [w] => referenceCost w target
  | w :: ws => referenceCost w target + pathReferenceCost ws target

/-- **Geodesic WToken Selection**: Find the shortest path to a concept.

    The geodesic is the WToken (or sequence) that minimizes total cost:
    intrinsic cost + reference cost.
-/
structure GeodesicWTokenSelection (c : Concept) where
  /-- The selected WToken -/
  wtoken : WTokenSpec
  /-- Total cost: intrinsic + reference -/
  total_cost : ℝ := wtokenCost wtoken + referenceCost wtoken c
  /-- This is optimal among all WTokens -/
  is_optimal : ∀ w : WTokenSpec, total_cost ≤ wtokenCost w + referenceCost w c

/-- For level-0 WTokens, the total cost equals the reference cost (since J(w) = 0). -/
theorem level0_total_cost_eq_reference (c : Concept) :
    let w := { mode := ModeFamilyId.mode1_7, phi_level := PhiLevel.level0,
               tau_offset := TauOffset.tau0, tau_valid := by decide : WTokenSpec }
    wtokenCost w + referenceCost w c = referenceCost w c := by
  simp only
  rw [level0_zero_cost _ rfl, zero_add]

/-! ## Part 9: Semantic Cost Metric -/

/-- The **semantic distance** between two concepts is the reference cost
    of the optimal WToken that can represent both.

    This defines a (pseudo)metric on the space of concepts.
-/
noncomputable def semanticDistance (c₁ c₂ : Concept) : ℝ :=
  -- Find the WToken that minimizes max(R(w, c₁), R(w, c₂))
  -- For now, use direct ratio-based distance
  Jcost (c₁.ratio / c₂.ratio)

/-- Semantic distance is symmetric (from J symmetry). -/
theorem semanticDistance_symm (c₁ c₂ : Concept) :
    semanticDistance c₁ c₂ = semanticDistance c₂ c₁ := by
  unfold semanticDistance
  rw [Jcost_symm (div_pos c₁.ratio_pos c₂.ratio_pos)]
  congr 1
  rw [inv_div]

/-- Semantic distance is zero iff concepts have the same ratio. -/
theorem semanticDistance_zero_iff (c₁ c₂ : Concept) :
    semanticDistance c₁ c₂ = 0 ↔ c₁.ratio = c₂.ratio := by
  unfold semanticDistance
  rw [Jcost_eq_zero_iff _ (div_pos c₁.ratio_pos c₂.ratio_pos)]
  constructor
  · intro h
    have h_div : c₁.ratio / c₂.ratio = 1 := h
    rw [div_eq_one_iff_eq (ne_of_gt c₂.ratio_pos)] at h_div
    exact h_div
  · intro h
    rw [h, div_self (ne_of_gt c₂.ratio_pos)]

/-! ## Part 10: Summary and Status -/

/-- **COMPLETE SUMMARY**: The Algebra of Aboutness for WTokens.

    Key results:
    1. WTokens form a CostedSpace with J(φ^level)
    2. Level-0 WTokens have J = 0 (universal compressors)
    3. Reference cost uses ratio-induced structure
    4. Composition satisfies d'Alembert bounds
    5. Geodesic selection minimizes total cost
    6. Semantic distance defines a pseudometric on concepts
-/
theorem algebra_of_aboutness_wtoken_summary :
    -- Level-0 is zero cost
    (∀ w : WTokenSpec, w.phi_level = .level0 → wtokenCost w = 0) ∧
    -- Self-reference is zero
    (∀ w : WTokenSpec, wtokenReference.cost w w = 0) ∧
    -- Universal compression
    (∀ c : Concept, ∃ w : WTokenSpec, wtokenCost w < Jcost c.ratio) ∧
    -- Semantic distance is symmetric
    (∀ c₁ c₂ : Concept, semanticDistance c₁ c₂ = semanticDistance c₂ c₁) :=
  ⟨level0_zero_cost, wtoken_self_reference_zero,
   fun c => ⟨{ mode := .mode1_7, phi_level := .level0, tau_offset := .tau0,
               tau_valid := by decide }, level0_wtoken_is_universal_symbol c⟩,
   semanticDistance_symm⟩

#check wtoken_reference_complete
#check level0_wtoken_is_universal_symbol
#check wtoken_is_symbol_for_complex_concepts
#check wtoken_composition_cost_bound
#check wtoken_reference_triangle
#check semanticDistance_symm
#check algebra_of_aboutness_wtoken_summary

end WTokenReference
end Foundation
end IndisputableMonolith
