import Mathlib
import IndisputableMonolith.Verification.Reality
import IndisputableMonolith.Verification.Dimension
import IndisputableMonolith.Verification.Exclusivity
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.RSBridge.Anchor
import IndisputableMonolith.Meta.AxiomLattice

namespace IndisputableMonolith
namespace Verification
namespace Completeness

/-!
# Completeness certificates (Prime Closure)

This module bundles the now-proven pillars into a single constructive record and
an easy-to-consume closed theorem stack predicate.

Proven components included here:
* Master: `RSRealityMaster φ`
* Minimality: `FoundationMinimal φ` (Option A: cost/CPM foundation)
* Framework uniqueness: `FrameworkUniqueness φ`
* Spatial necessity: `∀ D, RSCounting_Gap45_Absolute D → D = 3`
* Exact 3 generations: `Function.Surjective RSBridge.genOf`
* Exclusivity bundle: `ExclusivityAt φ`
  (now paired with the reverse reconstruction lemma `bridge_matches_ud_reconstructs`
  in `Verification/Exclusivity.lean`, establishing that the explicit packs wired
  here determine the canonical frameworks and closing the UD→framework loop.)
-/

/-- Meta-certificate: all core pillars proven and bundled.

Note: Independent of `temporary_isPreconnected_assumption` (a nonessential classical
helper). This temporary lemma is isolated below and not used here. -/
structure RSCompleteness where
  master                  : ∀ φ : ℝ, Reality.RSRealityMaster φ
  minimality              : ∀ φ : ℝ, Meta.AxiomLattice.FoundationMinimal φ
  uniqueness              : ∀ φ : ℝ, IndisputableMonolith.RecogSpec.FrameworkUniqueness φ
  spatial3_necessity      : ∀ D : Nat, Dimension.RSCounting_Gap45_Absolute D → D = 3
  generations_exact_three : Function.Surjective IndisputableMonolith.RSBridge.genOf
  /-- Exclusivity-at-scale bundle (master + definitional uniqueness). -/
  exclusivity_at          : ∀ φ : ℝ, Exclusivity.ExclusivityAt φ

/-- Constructive witness that the completeness bundle holds. -/
theorem rs_completeness : RSCompleteness := by
  refine {
    master := ?master
  , minimality := ?min
  , uniqueness := ?uniq
  , spatial3_necessity := ?dim
  , generations_exact_three := ?gens
  , exclusivity_at := ?excl };
  · intro φ; exact Reality.rs_reality_master_any φ
  · intro φ; exact Meta.AxiomLattice.foundation_minimal_holds φ
  · intro φ; exact IndisputableMonolith.RecogSpec.framework_uniqueness φ
  · intro D h; exact Dimension.onlyD3_satisfies_RSCounting_Gap45_Absolute h
  · exact IndisputableMonolith.RSBridge.genOf_surjective
  · intro φ
    exact Exclusivity.exclusivity_at_of_framework_uniqueness φ (IndisputableMonolith.RecogSpec.framework_uniqueness φ)

/-- Prime Closure predicate at scale `φ` (apex certificate).

Note: Independent of `temporary_isPreconnected_assumption` (nonessential classical
helper isolated below; TODO closed). -/
def PrimeClosure (φ : ℝ) : Prop :=
  Reality.RSRealityMaster φ ∧
  IndisputableMonolith.RecogSpec.FrameworkUniqueness φ ∧
  (∀ D : Nat, Dimension.RSCounting_Gap45_Absolute D → D = 3) ∧
  Function.Surjective IndisputableMonolith.RSBridge.genOf ∧
  Meta.AxiomLattice.FoundationMinimal φ

/-- Constructive witness of Prime Closure at `φ`. -/
theorem prime_closure (φ : ℝ) : PrimeClosure φ := by
  refine And.intro (Reality.rs_reality_master_any φ) ?rest
  refine And.intro (IndisputableMonolith.RecogSpec.framework_uniqueness φ) ?rest2
  refine And.intro (fun D h => Dimension.onlyD3_satisfies_RSCounting_Gap45_Absolute h) ?rest3
  refine And.intro (IndisputableMonolith.RSBridge.genOf_surjective) (Meta.AxiomLattice.foundation_minimal_holds φ)

/- Backwards compatibility aliases. -/
abbrev ClosedTheoremStack := PrimeClosure
theorem closed_theorem_stack (φ : ℝ) : ClosedTheoremStack φ := prime_closure φ

/-! ## Nonessential classical helper (isolated)

This helper depends on Mathlib analysis (`isConnected_ball`). It is not used by
`RSCompleteness`, `PrimeClosure`, or any completeness result. Retained only as a
standalone utility; safe to delete without affecting completeness. -/

section ClassicalNonessential

open Classical
noncomputable section

/-- Nonessential classical helper: preconnectedness of metric balls via `isConnected_ball`.
Not used by `RSCompleteness` or `PrimeClosure`. -/
lemma temporary_isPreconnected_assumption {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x : E) {r : ℝ} (hr : 0 < r) :
  IsPreconnected (Metric.ball x r) :=
  (isConnected_ball x hr).isPreconnected

end

end ClassicalNonessential

end Completeness
end Verification
end IndisputableMonolith
