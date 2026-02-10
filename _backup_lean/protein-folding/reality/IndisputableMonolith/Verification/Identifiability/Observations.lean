import Mathlib
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.RH.RS.Framework

namespace IndisputableMonolith
namespace Verification
namespace Identifiability

open IndisputableMonolith
open IndisputableMonolith.RH.RS

/-- Dimensionless observational ledger extracted at scale φ. -/
structure ObservedLedger (φ : ℝ) where
  alpha            : ℝ
  massRatios       : List ℝ
  mixingAngles     : List ℝ
  g2Muon           : ℝ
  strongCPNeutral  : Prop
  eightTickMinimal : Prop
  bornRule         : Prop
  boseFermi        : Prop

/-- Package an observed ledger from a universal φ‑closed target. -/
noncomputable def observedFromUD (φ : ℝ) (U : UniversalDimless φ) : ObservedLedger φ :=
{ alpha := U.alpha0
, massRatios := U.massRatios0
, mixingAngles := U.mixingAngles0
, g2Muon := U.g2Muon0
, strongCPNeutral := U.strongCP0
, eightTickMinimal := U.eightTick0
, bornRule := U.born0
, boseFermi := U.boseFermi0 }

/-- Package an observed ledger from a concrete bridge-side dimless pack. -/
noncomputable def observedFromPack (φ : ℝ) {L : Ledger} {B : Bridge L}
  (P : DimlessPack L B) : ObservedLedger φ :=
{ alpha := P.alpha
, massRatios := P.massRatios
, mixingAngles := P.mixingAngles
, g2Muon := P.g2Muon
, strongCPNeutral := P.strongCPNeutral
, eightTickMinimal := P.eightTickMinimal
, bornRule := P.bornRule
, boseFermi := P.boseFermi }

lemma observedFromPack_matches_to (φ : ℝ) {L : Ledger} {B : Bridge L}
  {P : DimlessPack L B} {U : UniversalDimless φ}
  (h : P.alpha = U.alpha0 ∧
      P.massRatios = U.massRatios0 ∧
      P.mixingAngles = U.mixingAngles0 ∧
      P.g2Muon = U.g2Muon0 ∧
      P.strongCPNeutral = U.strongCP0 ∧
      P.eightTickMinimal = U.eightTick0 ∧
      P.bornRule = U.born0 ∧
      P.boseFermi = U.boseFermi0) :
  observedFromPack φ (P:=P) = observedFromUD φ U := by
  rcases h with ⟨hα, hrest⟩
  rcases hrest with ⟨hmr, hrest⟩
  rcases hrest with ⟨hma, hrest⟩
  rcases hrest with ⟨hg2, hrest⟩
  rcases hrest with ⟨hscp, hrest⟩
  rcases hrest with ⟨het, hrest⟩
  rcases hrest with ⟨hborn, hbf⟩
  simp [observedFromPack, observedFromUD, hα, hmr, hma, hg2, hscp, het, hborn, hbf]

lemma observedFromPack_of_matches (φ : ℝ) {L : Ledger} {B : Bridge L}
  {P : DimlessPack L B}
  (h : P.alpha = (UD_explicit φ).alpha0 ∧
      P.massRatios = (UD_explicit φ).massRatios0 ∧
      P.mixingAngles = (UD_explicit φ).mixingAngles0 ∧
      P.g2Muon = (UD_explicit φ).g2Muon0 ∧
      P.strongCPNeutral = (UD_explicit φ).strongCP0 ∧
      P.eightTickMinimal = (UD_explicit φ).eightTick0 ∧
      P.bornRule = (UD_explicit φ).born0 ∧
      P.boseFermi = (UD_explicit φ).boseFermi0) :
  observedFromPack φ (P:=P) = observedFromUD φ (UD_explicit φ) :=
  observedFromPack_matches_to (φ:=φ) (P:=P) (U:=UD_explicit φ) h

/-- Deterministic bridge selector stub (parameterized hypothesis).
Provide any concrete bridge for a given zero‑parameter framework. -/
structure BridgeSelector (φ : ℝ) (F : ZeroParamFramework φ) where
  select : Bridge F.L

/-- Construct observations using an explicit pack on a provided bridge. -/
noncomputable def observeWithBridge (φ : ℝ) (F : ZeroParamFramework φ)
  (B : Bridge F.L) : ObservedLedger φ :=
  observedFromPack φ (P := dimlessPack_explicit φ F.L B)

/-! Classical gate (choice-dependent): the following definitions and lemmas
    use choice to pick bridges/packs. These are fenced to keep the MP-only
    envelope clear and are provided as fallbacks. -/

noncomputable section

open Classical

lemma observedFromPack_matches_explicit (φ : ℝ) {L : Ledger} (B : Bridge L) :
  observedFromPack φ (P:=Classical.choose (matches_explicit φ L B))
    = observedFromUD φ (UD_explicit φ) := by
  classical
  have h := Classical.choose_spec (matches_explicit φ L B)
  exact observedFromPack_of_matches (φ:=φ) h

noncomputable def someBridge (φ : ℝ) (F : ZeroParamFramework φ) : Bridge F.L :=
  Classical.choose F.hasEU.left

lemma someBridge_matches (φ : ℝ) (F : ZeroParamFramework φ) :
  ∃ U : UniversalDimless φ, Matches φ F.L (someBridge φ F) U := by
  classical
  exact Classical.choose_spec F.hasEU.left

/-- Canonical observation obtained by transporting the explicit pack supplied by
`Matches`.  This depends only on the ledger/discrete data carried by the
zero-parameter framework and the uniqueness theorems (T4/T5) establishing
`matches_explicit`. -/
noncomputable def observe (φ : ℝ) (F : ZeroParamFramework φ) : ObservedLedger φ :=
  observedFromPack φ
    (P:=Classical.choose (matches_explicit φ F.L (someBridge φ F)))

lemma observe_eq_ud (φ : ℝ) (F : ZeroParamFramework φ) :
  observe φ F = observedFromUD φ (UD_explicit φ) := by
  classical
  unfold observe
  simpa using observedFromPack_matches_explicit (φ:=φ) (B:=someBridge φ F)

lemma observe_with_explicit_pack (φ : ℝ) (F : ZeroParamFramework φ) :
  observedFromPack φ (P:=Classical.choose (matches_explicit φ F.L (someBridge φ F)))
    = observe φ F := rfl

lemma observe_def_with_explicit_pack (φ : ℝ) (F : ZeroParamFramework φ) :
  observe φ F =
    observedFromPack φ (P:=Classical.choose (matches_explicit φ F.L (someBridge φ F))) := rfl

lemma observe_eq_observedFromPack_explicit (φ : ℝ) (F : ZeroParamFramework φ) :
  observe φ F = observedFromPack φ
    (P:=Classical.choose (matches_explicit φ F.L (someBridge φ F))) := rfl

end  -- noncomputable classical fence

/-- Observational equality between zero-parameter frameworks at scale φ. -/
@[simp] def ObsEqual (φ : ℝ) (F G : ZeroParamFramework φ) : Prop :=
  observe φ F = observe φ G

lemma obs_equal_rfl (φ : ℝ) (F : ZeroParamFramework φ) : ObsEqual φ F F := rfl

lemma obs_equal_comm {φ : ℝ} {F G : ZeroParamFramework φ} :
  ObsEqual φ F G → ObsEqual φ G F := by
  intro h; simpa [ObsEqual] using h.symm

lemma obs_equal_trans {φ : ℝ}
  {F G H : ZeroParamFramework φ} :
  ObsEqual φ F G → ObsEqual φ G H → ObsEqual φ F H := by
  intro hFG hGH; simpa [ObsEqual] using hFG.trans hGH

end Identifiability
end Verification
end IndisputableMonolith
