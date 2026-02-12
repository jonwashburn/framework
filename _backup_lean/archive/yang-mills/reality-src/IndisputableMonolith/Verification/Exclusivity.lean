import Mathlib
import IndisputableMonolith.RH.RS.Spec
-- import IndisputableMonolith.RH.RS.Units
import IndisputableMonolith.Verification.Reality
import IndisputableMonolith.Verification.Identifiability.Observations

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity

open IndisputableMonolith
open IndisputableMonolith.RH.RS
open IndisputableMonolith.Verification
open IndisputableMonolith.Verification.Identifiability

/-!
This module elevates the PrimeClosure layer by formalizing:

1. A Prop-level notion of definitional equivalence between zero-parameter frameworks
   that, at minimum, subsumes the existing uniqueness up to units via the units
   quotient isomorphism.
2. Definitional uniqueness at a fixed scale φ, derived from the already proven
   `FrameworkUniqueness φ` (pairwise isomorphism up to units).
3. φ-pinning as a bundled uniqueness statement using the existing
   `phi_selection_unique_with_closure` witness.
4. An exclusivity-at-scale bundle that packages RSRealityMaster together with
   definitional uniqueness.
5. A reverse reconstruction principle: any bridge/pack that matches the explicit
   universal target `UD_explicit φ` reconstructs the canonical interpretation, closing
   the bi-directional interpretation loop. This complements the completeness upgrade
   (`Verification/Completeness.lean`) by showing that the explicit packs used there also
   determine the originating framework data.

This is a conservative upgrade: it does not add new axioms. It introduces
names for broader equivalence and shows that existing results imply the new
bundle under the units-quotient interpretation of definitional equivalence.
-/

/-! ### Definitional equivalence and uniqueness (Prop-level)

We now upgrade definitional equivalence beyond the mere existence of a units quotient
isomorphism. The refined witness records:

1. Observational equality of the extracted ledgers (bridge-invariant ledger agreement).
2. An explicit equivalence between the units quotients (retaining the classical result).
3. Canonical bridge interpretations bundling both the existential universal targets from
   the framework witnesses and their alignment with the explicit universal dimensionless
   pack, exposing the shared semantics behind the ledger equality and how each framework
   realizes the same universal data.

This bundled witness serves as a stepping stone toward full bi-interpretability: we
retain conservative uniqueness proofs, but now surface the interpretation data that a
future bi-interpretability upgrade will require.
-/

/-- Bridge interpretation data for a zero-parameter framework.

This bundles:

- a chosen bridge `bridge : Bridge F.L` (from the existence part of `F.hasEU`),
- a universal φ‑closed target `target : UniversalDimless φ` with a concrete bridge‑side
  `packTarget` that matches it (the existential `U` from `someBridge_matches`), and
- an explicit bridge‑side pack `packExplicit` that aligns component‑wise with the
  canonical universal `UD_explicit φ`.

Intuitively, `packTarget` witnesses the existential universal data provided by the
existence‑and‑uniqueness (up to units) scaffold, while `packExplicit` exposes the
canonical coordinates. The latter, together with observational equality results, gives
transparent reconstruction lemmas connecting the observed ledger to the canonical
interpretation. -/
structure BridgeInterpretation (φ : ℝ) (F : ZeroParamFramework φ) where
  bridge : Bridge F.L
  target : UniversalDimless φ
  packTarget : DimlessPack F.L bridge
  matchesTarget :
    packTarget.alpha = target.alpha0 ∧
    packTarget.massRatios = target.massRatios0 ∧
    packTarget.mixingAngles = target.mixingAngles0 ∧
    packTarget.g2Muon = target.g2Muon0 ∧
    packTarget.strongCPNeutral = target.strongCP0 ∧
    packTarget.eightTickMinimal = target.eightTick0 ∧
    packTarget.bornRule = target.born0 ∧
    packTarget.boseFermi = target.boseFermi0
  packExplicit : DimlessPack F.L bridge
  matchesExplicit :
    packExplicit.alpha = (UD_explicit φ).alpha0 ∧
    packExplicit.massRatios = (UD_explicit φ).massRatios0 ∧
    packExplicit.mixingAngles = (UD_explicit φ).mixingAngles0 ∧
    packExplicit.g2Muon = (UD_explicit φ).g2Muon0 ∧
    packExplicit.strongCPNeutral = (UD_explicit φ).strongCP0 ∧
    packExplicit.eightTickMinimal = (UD_explicit φ).eightTick0 ∧
    packExplicit.bornRule = (UD_explicit φ).born0 ∧
    packExplicit.boseFermi = (UD_explicit φ).boseFermi0

/-- Canonical bridge interpretation obtained from the existence‑and‑uniqueness witness for
    a zero‑parameter framework. -/
noncomputable def canonicalInterpretation (φ : ℝ) (F : ZeroParamFramework φ) :
    BridgeInterpretation φ F := by
  classical
  have hBridge := Identifiability.someBridge φ F
  have hTargetWitness := Identifiability.someBridge_matches φ F
  rcases hTargetWitness with ⟨target, htargetMatch⟩
  rcases htargetMatch with ⟨packTarget, hpackTarget⟩
  have hExplicitWitness := matches_explicit φ F.L hBridge
  rcases hExplicitWitness with ⟨packExplicit, hpackExplicit⟩
  refine
  {
    bridge := hBridge
  , target := target
  , packTarget := packTarget
  , matchesTarget := hpackTarget
  , packExplicit := packExplicit
  , matchesExplicit := hpackExplicit
  }

/-- Units quotient class of a bridge in a zero-parameter framework. -/
def unitsClass {φ : ℝ} (F : ZeroParamFramework φ) (B : Bridge F.L) :
    UnitsQuotCarrier F :=
  Quot.mk _ B

lemma unitsClass_eq_of_rel {φ : ℝ} (F : ZeroParamFramework φ)
    {B₁ B₂ : Bridge F.L} (h : F.eqv.Rel B₁ B₂) :
    unitsClass F B₁ = unitsClass F B₂ :=
  Quot.eq.2 h

/-- Canonical units quotient class realized by the canonical interpretation. -/
def canonicalUnitsClass (φ : ℝ) (F : ZeroParamFramework φ) :
    UnitsQuotCarrier F :=
  unitsClass F (canonicalInterpretation φ F).bridge

lemma canonicalUnitsClass_eq_unitsClass_of_rel
    (φ : ℝ) (F : ZeroParamFramework φ) {B : Bridge F.L}
    (h : F.eqv.Rel (canonicalInterpretation φ F).bridge B) :
    canonicalUnitsClass φ F = unitsClass F B :=
  unitsClass_eq_of_rel _ h

lemma unitsClass_eq_canonicalUnitsClass_of_rel
    (φ : ℝ) (F : ZeroParamFramework φ) {B : Bridge F.L}
    (h : F.eqv.Rel B (canonicalInterpretation φ F).bridge) :
    unitsClass F B = canonicalUnitsClass φ F :=
  unitsClass_eq_of_rel _ h

lemma canonicalInterpretation_matches_ud_unique_units
    (φ : ℝ) (F : ZeroParamFramework φ) {B' : Bridge F.L}
    (hMatch : Matches φ F.L B' (UD_explicit φ)) :
    canonicalUnitsClass φ F = unitsClass F B' := by
  have hRel :=
    canonicalInterpretation_matches_ud_unique (φ:=φ) (F:=F) (B':=B') hMatch
  simpa using canonicalUnitsClass_eq_unitsClass_of_rel (φ:=φ) (F:=F) hRel

structure DefinitionalWitness (φ : ℝ)
  (F G : ZeroParamFramework φ) where
  obsEqual : Identifiability.ObsEqual φ F G
  unitsIso : UnitsQuotCarrier F ≃ UnitsQuotCarrier G
  unitsCanonical :
    unitsIso (canonicalUnitsClass φ F) = canonicalUnitsClass φ G
  interpF : BridgeInterpretation φ F
  interpG : BridgeInterpretation φ G
  obsF : Identifiability.observe φ F =
    Identifiability.observedFromPack φ (P:=interpF.packExplicit)
  obsG : Identifiability.observe φ G =
    Identifiability.observedFromPack φ (P:=interpG.packExplicit)
  obsShared : Identifiability.observedFromPack φ (P:=interpF.packExplicit)
    = Identifiability.observedFromPack φ (P:=interpG.packExplicit)

/-! ### Canonical units-quotient equivalence and its action on canonical classes

We expose the explicit equivalence `unitsQuot_equiv F G` between the units quotients
of two zero-parameter frameworks (constructed from one-point + nonempty). It carries
the canonical class of `F` to the canonical class of `G` by one-pointness. -/

@[simp] lemma unitsQuot_equiv_maps_canonical (φ : ℝ)
    (F G : ZeroParamFramework φ) :
  unitsQuot_equiv F G (canonicalUnitsClass φ F) = canonicalUnitsClass φ G := by
  -- In a one-point quotient, every element equals the canonical class.
  have hG1 : OnePoint (UnitsQuotCarrier G) := zpf_unitsQuot_onePoint G
  exact hG1 _ _

/-- Naturality under composition on canonical classes.
    Transport along `F → G → H` equals the direct transport `F → H`. -/
@[simp] lemma unitsQuot_equiv_maps_canonical_comp (φ : ℝ)
    (F G H : ZeroParamFramework φ) :
  (unitsQuot_equiv G H)
      ((unitsQuot_equiv F G) (canonicalUnitsClass φ F))
    = (unitsQuot_equiv F H) (canonicalUnitsClass φ F) := by
  simp [Equiv.trans, unitsQuot_equiv_apply]

/-- Triple‑naturality: direct transport equals composite transport via an
intermediate framework. -/
@[simp] lemma units_canonical_triple_natural (φ : ℝ)
    (F G H : ZeroParamFramework φ) :
  (unitsQuot_equiv F H) (canonicalUnitsClass φ F)
    = (unitsQuot_equiv G H)
        ((unitsQuot_equiv F G) (canonicalUnitsClass φ F)) := by
  simpa using (unitsQuot_equiv_maps_canonical_comp (φ:=φ) F G H).symm

/-/ Symmetry under automorphisms: any end-equivalence of the units quotient
    fixes the canonical class (by one-pointness). -/
@[simp] lemma units_canonical_invariant_under_aut (φ : ℝ)
    (F : ZeroParamFramework φ)
    (e : UnitsQuotCarrier F ≃ UnitsQuotCarrier F) :
  e (canonicalUnitsClass φ F) = canonicalUnitsClass φ F := by
  have h1 : OnePoint (UnitsQuotCarrier F) := zpf_unitsQuot_onePoint F
  exact h1 _ _

/-- Coherence bundle for canonical units classes at scale `φ`.
    - Symmetry: for any framework `F`, every automorphism of `UnitsQuotCarrier F`
      fixes the canonical units class.
    - Naturality: for any `F G`, the canonical equivalence carries the canonical
      class of `F` to that of `G`.

    This packages the stable API expected by downstream modules. -/
theorem units_class_coherence (φ : ℝ) :
  (∀ F : ZeroParamFramework φ,
     ∀ e : UnitsQuotCarrier F ≃ UnitsQuotCarrier F,
       e (canonicalUnitsClass φ F) = canonicalUnitsClass φ F)
  ∧
  (∀ F G : ZeroParamFramework φ,
     unitsQuot_equiv F G (canonicalUnitsClass φ F) = canonicalUnitsClass φ G) := by
  constructor
  · intro F e
    simpa using (units_canonical_invariant_under_aut (φ:=φ) (F:=F) e)
  · intro F G
    simpa using (unitsQuot_equiv_maps_canonical (φ:=φ) F G)

/-- Convenience: a bridge's units class equals the canonical class iff the bridge
is related by the units relation to the canonical bridge. -/
lemma unitsClass_eq_canonical_iff
    (φ : ℝ) (F : ZeroParamFramework φ) {B : Bridge F.L} :
  unitsClass F B = canonicalUnitsClass φ F
    ↔ F.eqv.Rel B (canonicalInterpretation φ F).bridge := by
  constructor
  · intro h
    -- Equality of classes implies the relation by `Quot.eq.1`.
    simpa [canonicalUnitsClass] using (Quot.eq.1 h)
  · intro h
    -- Relation implies equality by `Quot.eq.2` via the helper lemma.
    simpa using
      (unitsClass_eq_canonicalUnitsClass_of_rel (φ:=φ) (F:=F) (B:=B) h)

lemma BridgeInterpretation.observedFromPack_target_eq
    (interp : BridgeInterpretation φ F) :
  Identifiability.observedFromPack φ (P:=interp.packTarget)
    = Identifiability.observedFromUD φ interp.target := by
  simpa using
    Identifiability.observedFromPack_matches_to (φ:=φ)
      (P:=interp.packTarget) (U:=interp.target) interp.matchesTarget

lemma BridgeInterpretation.observedFromPack_explicit_eq_ud (interp : BridgeInterpretation φ F) :
  Identifiability.observedFromPack φ (P:=interp.packExplicit)
    = Identifiability.observedFromUD φ (UD_explicit φ) := by
  simpa using
    Identifiability.observedFromPack_matches_to (φ:=φ)
      (P:=interp.packExplicit) (U:=UD_explicit φ) interp.matchesExplicit

/-- Reconstruction: the observed ledger coincides with the ledger built from the
canonical interpretation's explicit pack. -/
lemma canonicalInterpretation_observe_eq (φ : ℝ) (F : ZeroParamFramework φ) :
  Identifiability.observe φ F =
    Identifiability.observedFromPack φ
      (P:=(canonicalInterpretation φ F).packExplicit) := by
  classical
  have hObs := Identifiability.observe_eq_ud φ F
  have hPack :=
    (BridgeInterpretation.observedFromPack_explicit_eq_ud
      (φ:=φ) (F:=F) (canonicalInterpretation φ F))
  exact hObs.trans hPack.symm

/-- The canonical interpretation's chosen bridge matches the explicit universal
dimensionless target `UD_explicit φ` (via its `packExplicit`). -/
lemma canonicalInterpretation_matches_ud (φ : ℝ) (F : ZeroParamFramework φ) :
  Matches φ F.L (canonicalInterpretation φ F).bridge (UD_explicit φ) := by
  classical
  refine Exists.intro (canonicalInterpretation φ F).packExplicit ?h
  simpa using (canonicalInterpretation φ F).matchesExplicit

/-- Uniqueness up to units: any bridge that matches `UD_explicit φ` is units‑equivalent
to the canonical interpretation's bridge. -/
lemma canonicalInterpretation_matches_ud_unique (φ : ℝ) (F : ZeroParamFramework φ) :
  ∀ {B' : Bridge F.L},
    Matches φ F.L B' (UD_explicit φ) →
    F.eqv.Rel (canonicalInterpretation φ F).bridge B' := by
  intro B' _hMatch
  -- Uniqueness up to units is bundled in `F.hasEU.right`.
  exact F.hasEU.right (canonicalInterpretation φ F).bridge B'

/-- Build a bridge interpretation directly from a bridge/pack that matches
`UD_explicit φ`. This witnesses the reverse leg of the canonical construction:
starting from the explicit match, we recover the same observational data and the
bridge sits in the canonical units class. The cost/strict-minimality apparatus
from identifiability is reused to route the observational equality, completing
the "bi" loop advertised in the exclusivity upgrade and complementing the
completeness report (`URCAdapters/Completeness.lean`). -/
noncomputable def BridgeInterpretation.ofExplicitMatch (φ : ℝ) (F : ZeroParamFramework φ)
    {B : Bridge F.L} (P : DimlessPack F.L B)
    (hMatch :
      P.alpha = (UD_explicit φ).alpha0 ∧
      P.massRatios = (UD_explicit φ).massRatios0 ∧
      P.mixingAngles = (UD_explicit φ).mixingAngles0 ∧
      P.g2Muon = (UD_explicit φ).g2Muon0 ∧
      P.strongCPNeutral = (UD_explicit φ).strongCP0 ∧
      P.eightTickMinimal = (UD_explicit φ).eightTick0 ∧
      P.bornRule = (UD_explicit φ).born0 ∧
      P.boseFermi = (UD_explicit φ).boseFermi0) :
    BridgeInterpretation φ F :=
{
  bridge := B
, target := UD_explicit φ
, packTarget := P
, matchesTarget := hMatch
, packExplicit := P
, matchesExplicit := hMatch
}

/-- Reverse reconstruction: any bridge whose explicit pack matches `UD_explicit φ`
recovers the original framework's observational ledger and lands in the
canonical units class. This closes the bi-directional interpretation loop using
the strict-minimality/cost pipeline (cost zero ⇒ observed ledger matches
`UD_explicit φ`), showing that the explicit packs tracked in the completeness
upgrade indeed determine the framework. -/
lemma bridge_matches_ud_reconstructs
    (φ : ℝ) (F : ZeroParamFramework φ) {B : Bridge F.L}
    (P : DimlessPack F.L B)
    (hMatch :
      P.alpha = (UD_explicit φ).alpha0 ∧
      P.massRatios = (UD_explicit φ).massRatios0 ∧
      P.mixingAngles = (UD_explicit φ).mixingAngles0 ∧
      P.g2Muon = (UD_explicit φ).g2Muon0 ∧
      P.strongCPNeutral = (UD_explicit φ).strongCP0 ∧
      P.eightTickMinimal = (UD_explicit φ).eightTick0 ∧
      P.bornRule = (UD_explicit φ).born0 ∧
      P.boseFermi = (UD_explicit φ).boseFermi0) :
    Identifiability.observe φ F
      = Identifiability.observedFromPack φ (P:=P)
      ∧ canonicalUnitsClass φ F = unitsClass F B := by
  classical
  have hCost : Identifiability.costOf φ F = 0 :=
    Identifiability.costOf_eq_zero (φ:=φ) (F:=F)
  have hObsUD :=
    Identifiability.observe_eq_ud_of_cost_zero (φ:=φ) (F:=F) hCost
  have hPackUD :=
    Identifiability.observedFromPack_of_matches (φ:=φ) (P:=P) hMatch
  have hMatchBridge : Matches φ F.L B (UD_explicit φ) := ⟨P, hMatch⟩
  have hUnits :=
    canonicalInterpretation_matches_ud_unique_units (φ:=φ) (F:=F)
      (B':=B) hMatchBridge
  refine ⟨?_, hUnits⟩
  exact hObsUD.trans hPackUD.symm

/-- Reverse reconstruction complementing `canonicalInterpretation_observe_eq`:
any bridge that matches `UD_explicit φ` (via some explicit pack) produces the
framework's observed ledger and is units-equivalent to the canonical bridge.
This witnesses the "backward" leg of bi-interpretability. -/
lemma interpretable_from_ud_match
    (φ : ℝ) (F : ZeroParamFramework φ) {B : Bridge F.L}
    (hMatch : Matches φ F.L B (UD_explicit φ)) :
    ∃ P : DimlessPack F.L B,
      Identifiability.observe φ F =
        Identifiability.observedFromPack φ (P:=P) ∧
      Identifiability.observe φ F =
        Identifiability.observedFromUD φ (UD_explicit φ) ∧
      F.eqv.Rel (canonicalInterpretation φ F).bridge B := by
  classical
  rcases hMatch with ⟨P, hP⟩
  have hRecon :=
    bridge_matches_ud_reconstructs (φ:=φ) (F:=F) (B:=B) (P:=P) hP
  have hPackUD :=
    Identifiability.observedFromPack_of_matches (φ:=φ) (P:=P) hP
  refine ⟨P, ?_, ?_, ?_⟩
  · exact hRecon.left
  · exact hRecon.left.trans hPackUD
  · exact canonicalInterpretation_matches_ud_unique (φ:=φ) (F:=F)
      (B':=B) ⟨P, hP⟩

/-- Reconstruction Principle (UD→Framework): from any `UD_explicit φ` match we recover
the canonical ledger and the canonical units class. This packages the reverse
direction so downstream modules can cite it directly alongside the forward
`canonicalInterpretation_*` lemmas. -/
lemma reconstruction_from_ud_match
    (φ : ℝ) (F : ZeroParamFramework φ) {B : Bridge F.L}
    (hMatch : Matches φ F.L B (UD_explicit φ)) :
    Identifiability.observe φ F =
      Identifiability.observedFromUD φ (UD_explicit φ) ∧
    canonicalUnitsClass φ F = unitsClass F B := by
  classical
  rcases hMatch with ⟨P, hP⟩
  have hRecon :=
    bridge_matches_ud_reconstructs (φ:=φ) (F:=F) (B:=B) (P:=P) hP
  have hPackUD :=
    Identifiability.observedFromPack_of_matches (φ:=φ) (P:=P) hP
  exact ⟨hRecon.left.trans hPackUD, hRecon.right⟩

/-- Naturality/compositionality for UD matches: any two bridges that match
`UD_explicit φ` yield the same units class and their explicit packs produce the
same observed ledger. -/
lemma reconstruction_natural_ud
    (φ : ℝ) (F : ZeroParamFramework φ)
    {B₁ B₂ : Bridge F.L}
    (h₁ : Matches φ F.L B₁ (UD_explicit φ))
    (h₂ : Matches φ F.L B₂ (UD_explicit φ)) :
    unitsClass F B₁ = unitsClass F B₂ ∧
    ∃ (P₁ : DimlessPack F.L B₁) (P₂ : DimlessPack F.L B₂),
      Identifiability.observedFromPack φ (P:=P₁)
        = Identifiability.observedFromPack φ (P:=P₂) := by
  classical
  rcases h₁ with ⟨P₁, hP₁⟩
  rcases h₂ with ⟨P₂, hP₂⟩
  -- Units classes agree via uniqueness up to units
  have hU1 :=
    canonicalInterpretation_matches_ud_unique_units (φ:=φ) (F:=F) (B':=B₁) ⟨P₁, hP₁⟩
  have hU2 :=
    canonicalInterpretation_matches_ud_unique_units (φ:=φ) (F:=F) (B':=B₂) ⟨P₂, hP₂⟩
  have hUnits : unitsClass F B₁ = unitsClass F B₂ := by
    simpa using hU1.symm.trans hU2
  -- Both packs produce the UD ledger, hence they agree
  have hL1 := Identifiability.observedFromPack_of_matches (φ:=φ) (P:=P₁) hP₁
  have hL2 := Identifiability.observedFromPack_of_matches (φ:=φ) (P:=P₂) hP₂
  refine ⟨hUnits, ?_⟩
  exact ⟨P₁, P₂, hL1.trans hL2.symm⟩

def DefinitionalEquivalence (φ : ℝ)
  (F G : ZeroParamFramework φ) : Prop :=
  Nonempty (DefinitionalWitness φ F G)

def DefinitionalUniqueness (φ : ℝ) : Prop :=
  ∀ F G : ZeroParamFramework φ, DefinitionalEquivalence φ F G

/‑! Units-quotient isomorphism already available implies definitional equivalence. -/
/-! Strengthened: use the canonical `unitsQuot_equiv` so the witness exposes an
explicit equivalence (not just its existence). -/
theorem units_iso_implies_definitional
  {φ : ℝ} (F G : ZeroParamFramework φ)
  (hObs : Identifiability.ObsEqual φ F G)
  (hIso : Nonempty (UnitsQuotCarrier F ≃ UnitsQuotCarrier G)) :
  DefinitionalEquivalence φ F G := by
  classical
  -- Use the canonical equivalence built from one-point + nonempty.
  let e : UnitsQuotCarrier F ≃ UnitsQuotCarrier G := unitsQuot_equiv F G
  set interpF := canonicalInterpretation φ F
  set interpG := canonicalInterpretation φ G
  have hFObs := Identifiability.observe_eq_ud φ F
  have hGObs := Identifiability.observe_eq_ud φ G
  have hFpack := (BridgeInterpretation.observedFromPack_explicit_eq_ud (φ:=φ) (F:=F) interpF)
  have hGpack := (BridgeInterpretation.observedFromPack_explicit_eq_ud (φ:=φ) (F:=G) interpG)
  refine ⟨⟨
    hObs
      , e
      , by
          -- By one-pointness, the canonical equivalence sends canonical class to canonical class.
          simpa using unitsQuot_equiv_maps_canonical (φ:=φ) F G
      , canonicalInterpretation φ F
      , canonicalInterpretation φ G
  , hFObs.trans hFpack.symm
  , hGObs.trans hGpack.symm
  , hFpack.trans hGpack.symm
  ⟩⟩

/‑! Framework uniqueness ⇒ Definitional uniqueness (conservative widening). -/
theorem definitional_uniqueness_of_framework_uniqueness
  {φ : ℝ} (hFU : FrameworkUniqueness φ) :
  DefinitionalUniqueness φ := by
  intro F G
  classical
  have hF := Identifiability.observe_eq_ud φ F
  have hG := Identifiability.observe_eq_ud φ G
  have hObs : Identifiability.ObsEqual φ F G := by
    simpa [Identifiability.ObsEqual, hF, hG]
  exact units_iso_implies_definitional F G hObs (hFU F G)

/‑! ### φ pinning (exists unique φ with selection and Recognition_Closure) -/

def PhiPinned : Prop :=
  ∃! φ : ℝ, PhiSelection φ ∧ Recognition_Closure φ

theorem phi_pinned : PhiPinned := by
  -- Reuse the generator-level uniqueness with closure
  simpa [PhiPinned] using
    IndisputableMonolith.URCGenerators.phi_selection_unique_with_closure

/‑! ### Exclusivity-at-scale bundle

We package "RS measures reality" together with definitional uniqueness at a given
scale φ. This expresses the intended exclusivity claim at that scale under the
conservative definitional equivalence.
-/

structure ExclusivityAt (φ : ℝ) where
  master      : Reality.RSRealityMaster φ
  defUnique   : DefinitionalUniqueness φ

theorem exclusivity_at_of_framework_uniqueness (φ : ℝ)
  (hFU : FrameworkUniqueness φ) :
  ExclusivityAt φ := by
  refine {
    master := ?m
  , defUnique := ?d };
  · exact Reality.rs_reality_master_any φ
  · exact definitional_uniqueness_of_framework_uniqueness hFU

/‑! ### Global "exclusive reality" statement (once-and-for-all) -/

/-- There exists a unique scale φ such that φ is pinned (selection+closure)
    and RS exhibits exclusivity at that scale (master + definitional uniqueness). -/
def ExclusiveReality : Prop :=
  ∃! φ : ℝ, (PhiSelection φ ∧ Recognition_Closure φ) ∧ ExclusivityAt φ

theorem exclusive_reality_holds : ExclusiveReality := by
  -- Start from the pinned φ (selection ∧ closure) uniqueness
  rcases phi_pinned with ⟨φ⋆, hpack, huniq⟩
  -- Provide the exclusivity witness at φ⋆ using framework uniqueness
  have hFU : FrameworkUniqueness φ⋆ := framework_uniqueness φ⋆
  have hExcl : ExclusivityAt φ⋆ := exclusivity_at_of_framework_uniqueness φ⋆ hFU
  refine Exists.intro φ⋆ ?hexact
  refine And.intro ?hpack ?huniq'
  · exact And.intro hpack hExcl
  · intro x hx
    -- Uniqueness projects through: selection+closure component pins x = φ⋆
    -- since huniq is uniqueness for (PhiSelection x ∧ Recognition_Closure x)
    have hx_eq : x = φ⋆ := huniq x hx.left
    exact hx_eq

/-! ### Bi‑interpretability (at scale φ)

We now package, beside `ExclusiveReality`, a higher‑level record bundling both
reconstruction directions and the units‑equivalence data that Completeness/Reports
already thread:

1. Observational equality for any two zero‑parameter frameworks (via UD ledger).
2. Forward reconstruction: `observe` equals the canonical explicit pack.
3. Reverse reconstruction to UD: `observe` equals the canonical universal ledger.
4. Canonical bridge matches the explicit universal target `UD_explicit φ`.
5. Reverse pack→framework reconstruction: any explicit match yields the observed
   ledger and lands in the canonical units class.
6. Units‑quotient equivalences between any two frameworks (from framework uniqueness).

Roadmap toward ultimate closure (tracked for follow‑up work):
* Categorical equivalence: functorial inverse between frameworks and universal
  targets (coherence of canonical units classes is handled by `units_class_coherence`).
* Dual‑agent integration: align forward scripts with the reverse categorical map.
-/

/-- Bi‑interpretability bundle at scale `φ`.

Fields provide observational equality, both reconstruction directions, a canonical
bridge match to `UD_explicit φ`, a reverse reconstruction from any explicit match
back to the observed ledger together with units‑class identification, and a
provider of units‑quotient equivalences for any two frameworks. -/
structure BiInterpretabilityAt (φ : ℝ) where
  obsEqual :
    ∀ F G : ZeroParamFramework φ, Identifiability.ObsEqual φ F G
  forward :
    ∀ F : ZeroParamFramework φ,
      Identifiability.observe φ F =
        Identifiability.observedFromPack φ
          (P:=(canonicalInterpretation φ F).packExplicit)
  reverseUD :
    ∀ F : ZeroParamFramework φ,
      Identifiability.observe φ F =
        Identifiability.observedFromUD φ (UD_explicit φ)
  canonicalMatches :
    ∀ F : ZeroParamFramework φ,
      Matches φ F.L (canonicalInterpretation φ F).bridge (UD_explicit φ)
  reconstructsFromExplicit :
    ∀ F : ZeroParamFramework φ
      {B : Bridge F.L} (P : DimlessPack F.L B),
      (P.alpha = (UD_explicit φ).alpha0 ∧
       P.massRatios = (UD_explicit φ).massRatios0 ∧
       P.mixingAngles = (UD_explicit φ).mixingAngles0 ∧
       P.g2Muon = (UD_explicit φ).g2Muon0 ∧
       P.strongCPNeutral = (UD_explicit φ).strongCP0 ∧
       P.eightTickMinimal = (UD_explicit φ).eightTick0 ∧
       P.bornRule = (UD_explicit φ).born0 ∧
       P.boseFermi = (UD_explicit φ).boseFermi0) →
      Identifiability.observe φ F =
        Identifiability.observedFromPack φ (P:=P)
      ∧ canonicalUnitsClass φ F = unitsClass F B
  unitsIso :
    ∀ F G : ZeroParamFramework φ,
      Nonempty (UnitsQuotCarrier F ≃ UnitsQuotCarrier G)

/-- Construct the bi‑interpretability bundle from framework uniqueness. -/
theorem biInterpretability_at_of_framework_uniqueness (φ : ℝ)
  (hFU : FrameworkUniqueness φ) :
  BiInterpretabilityAt φ := by
  classical
  refine
  { obsEqual := ?obs
  , forward := ?fwd
  , reverseUD := ?rev
  , canonicalMatches := ?cm
  , reconstructsFromExplicit := ?recon
  , unitsIso := ?iso };
  · intro F G
    have hF := Identifiability.observe_eq_ud φ F
    have hG := Identifiability.observe_eq_ud φ G
    simpa [Identifiability.ObsEqual, hF, hG]
  · intro F
    simpa using (canonicalInterpretation_observe_eq (φ:=φ) F)
  · intro F
    simpa using (Identifiability.observe_eq_ud (φ:=φ) (F:=F))
  · intro F
    simpa using (canonicalInterpretation_matches_ud (φ:=φ) F)
  · intro F B P hMatch
    simpa using
      (bridge_matches_ud_reconstructs (φ:=φ) (F:=F) (B:=B) (P:=P) hMatch)
  · intro F G
    exact hFU F G

/-- Global exclusive reality upgraded with the bi‑interpretability bundle.

This strengthens `ExclusiveReality` by additionally bundling the bi‑interpretability
data at the pinned `φ`. It remains conservative (no new axioms). The symmetry/coherence
of the canonical units class is now packaged by `units_class_coherence`, and a short
categorical-style equivalence can be layered on top if needed. -/
def ExclusiveRealityPlus : Prop :=
  ∃! φ : ℝ,
    (PhiSelection φ ∧ Recognition_Closure φ) ∧ ExclusivityAt φ ∧ BiInterpretabilityAt φ

theorem exclusive_reality_plus_holds : ExclusiveRealityPlus := by
  -- Start from the pinned φ (selection ∧ closure) uniqueness
  rcases phi_pinned with ⟨φ⋆, hpack, huniq⟩
  -- Provide witnesses at φ⋆ using framework uniqueness
  have hFU : FrameworkUniqueness φ⋆ := framework_uniqueness φ⋆
  have hExcl : ExclusivityAt φ⋆ := exclusivity_at_of_framework_uniqueness φ⋆ hFU
  have hBi   : BiInterpretabilityAt φ⋆ :=
    biInterpretability_at_of_framework_uniqueness φ⋆ hFU
  refine Exists.intro φ⋆ ?hexact
  refine And.intro ?hpack ?huniq'
  · exact And.intro hpack (And.intro hExcl hBi)
  · intro x hx
    -- Uniqueness projects through the (selection ∧ closure) component
    have hx_eq : x = φ⋆ := huniq x hx.left
    exact hx_eq

end Exclusivity
end Verification
end IndisputableMonolith
