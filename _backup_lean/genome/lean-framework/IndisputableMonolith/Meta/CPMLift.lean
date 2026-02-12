import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.CPM.LawOfExistence
import IndisputableMonolith.Meta.MPChain
import IndisputableMonolith.Patterns
import IndisputableMonolith.LedgerUnits
import IndisputableMonolith.Potential
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Verification.T5ExportsLight
import IndisputableMonolith.Verification.Necessity.AtomicTick
import IndisputableMonolith.Constants
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.Verification.Reality
import IndisputableMonolith.URCGenerators
import IndisputableMonolith.URCAdapters.TcGrowth

namespace IndisputableMonolith
namespace Meta

/-- Bundle MP together with a concrete CPM constants witness and basic positivity. -/
structure MPCPM where
  mp  : Recognition.MP
  C   : CPM.LawOfExistence.Constants
  pos : 0 < C.Knet ∧ 0 < C.Cproj ∧ 0 < C.Ceng

namespace MPCPM

/-- Lift an `MPCPM` bundle into the MPDerivationChain interface used by FromMP. -/
noncomputable def toChain (X : MPCPM) : MPDerivationChain :=
{ mp := X.mp
, steps :=
    let t2_build :=
      (fun (M : Recognition.RecognitionStructure)
           (hZero : IndisputableMonolith.Verification.Necessity.DiscreteNecessity.HasAlgorithmicSpec M.U)
           (hNonempty : Nonempty M.U) =>
        IndisputableMonolith.Verification.Necessity.AtomicTickNecessity.atomicTickFromZeroParams M hZero hNonempty);
    let t2_noconc :=
      (fun (M : Recognition.RecognitionStructure)
           (hZero : IndisputableMonolith.Verification.Necessity.DiscreteNecessity.HasAlgorithmicSpec M.U)
           (hNonempty : Nonempty M.U)
           (t : Nat) (u v : M.U)
           (hu : Recognition.AtomicTick.postedAt (M:=M) t u)
           (hv : Recognition.AtomicTick.postedAt (M:=M) t v) =>
        by have _inst : Recognition.AtomicTick M := t2_build M hZero hNonempty; exact Recognition.T2_atomicity (M:=M) t u v hu hv);
    let t3_cons :=
      (fun (M : Recognition.RecognitionStructure) (L : Recognition.Ledger M)
           (hbal : ∀ u, L.debit u = L.credit u) =>
        { conserve := (fun (ch : Recognition.Chain M) (_h : ch.head = ch.last) =>
            Recognition.chainFlux_zero_of_balanced (M:=M) L ch hbal) } :
        ∀ (M : Recognition.RecognitionStructure) (L : Recognition.Ledger M),
          (∀ u, L.debit u = L.credit u) → Recognition.Conserves L);
    let t3_closed :=
      (fun (M : Recognition.RecognitionStructure)
           (L : Recognition.Ledger M) (_ : Recognition.Conserves L)
           (ch : Recognition.Chain M) (h : ch.head = ch.last) =>
        Recognition.chainFlux_zero_of_loop (M:=M) L ch h);
    let t4_uni :=
      (fun (M : Recognition.RecognitionStructure) (δ : ℤ)
           (p q : IndisputableMonolith.Potential.Pot M)
           (hp : IndisputableMonolith.Potential.DE (M:=M) δ p)
           (hq : IndisputableMonolith.Potential.DE (M:=M) δ q)
           (x0 : M.U) (hbase : p x0 = q x0) {y} (hreach : Causality.Reaches (IndisputableMonolith.Potential.Kin M) x0 y) =>
        IndisputableMonolith.Potential.T4_unique_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) (y:=y) hbase hreach);
    let t5_uni :=
      (fun (F : ℝ → ℝ)
           (h : (∀ {x}, 0 < x → F x = F x⁻¹) ∧ F 1 = 0 ∧
                (deriv (deriv (F ∘ Real.exp)) 0 = 1) ∧
                Continuous (fun t => F (Real.exp t)) ∧
                IndisputableMonolith.Cost.FunctionalEquation.DirectCoshAdd (fun t => F (Real.exp t))) =>
        IndisputableMonolith.Verification.T5ExportsLight.t5_uniqueness F h);
    { t2_build_atomicTick := t2_build
    , t2_no_concurrency := t2_noconc
    , t3_conserves_of_balanced := t3_cons
    , t3_closed_flux := t3_closed
    , t4_exact_potential := t4_uni
    , t5_unique_cost := t5_uni }
, gap45 := fun φ => RecogSpec.fortyfive_gap_spec_holds φ
, inevitabilityDimless := fun φ => RecogSpec.inevitability_dimless_holds φ
, inevitabilityAbsolute := fun φ => RecogSpec.inevitability_absolute_holds φ
, recognitionComputation := IndisputableMonolith.URCAdapters.tc_growth_holds
, uniqueCalibration := fun L B A => RecogSpec.uniqueCalibration_any L B A
, meetsBands := fun L B U => RecogSpec.meetsBands_any_default L B U
, bridgeFactorizes := IndisputableMonolith.Verification.bridge_factorizes
, certificateFamily :=
    fun φ =>
      by
        classical
        rcases IndisputableMonolith.URCGenerators.demo_generators φ with ⟨Cfam, hCfam⟩
        refine ⟨Cfam, And.intro hCfam ?_⟩
        simpa [IndisputableMonolith.URCGenerators.demo_generators]
, realityBundle := fun φ =>
    IndisputableMonolith.Verification.Reality.rs_measures_reality_any φ
, recognitionClosure := fun φ => RecogSpec.recognition_closure_any φ
, rsRealityMaster := fun φ => IndisputableMonolith.Verification.Reality.rs_reality_master_any φ }

/-- Canonical RS CPM bundle: MP with cone-projection constants. -/
noncomputable def canonical : MPCPM :=
{ mp := Recognition.mp_holds
, C := CPM.LawOfExistence.RS.coneConstants
, pos := by
    -- Knet=1>0, Cproj=2>0, Ceng=1>0
    simp [CPM.LawOfExistence.RS.cone_Ceng_eq_one,
          CPM.LawOfExistence.RS.cone_Knet_eq_one,
          CPM.LawOfExistence.RS.cone_Cproj_eq_two]
}

end MPCPM

end Meta
end IndisputableMonolith
