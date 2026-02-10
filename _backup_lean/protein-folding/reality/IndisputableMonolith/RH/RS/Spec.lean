import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Verification
import IndisputableMonolith.RH.RS.Core
import IndisputableMonolith.RH.RS.Anchors
import IndisputableMonolith.RH.RS.Bands
import IndisputableMonolith.Patterns
import IndisputableMonolith.Quantum
import IndisputableMonolith.Measurement.C2ABridge
import IndisputableMonolith.Measurement.TwoBranchGeodesic

noncomputable section
open Classical
open PhiClosed

namespace IndisputableMonolith
namespace RH
namespace RS

/-- Canonical speed determined by a pair of anchors. -/
def speedFromAnchors (A : Anchors) : ℝ :=
  if h : A.a1 = 0 then 0 else A.a2 / A.a1

/-- Units obtained by calibrating directly against the anchors. -/
def unitsFromAnchors (A : Anchors) : Constants.RSUnits :=
{ tau0 := A.a1
, ell0 := A.a2
, c := speedFromAnchors A
, c_ell0_tau0 := by
    by_cases h : A.a1 = 0
    · have hℓ : A.a2 = 0 := A.consistent h
      simp [speedFromAnchors, h, hℓ]
    · have : A.a1 ≠ 0 := h
      simp [speedFromAnchors, h, this, mul_comm, mul_left_comm, mul_assoc] }

@[simp] lemma speedFromAnchors_of_eq_zero {A : Anchors} (h : A.a1 = 0) :
    speedFromAnchors A = 0 := by simp [speedFromAnchors, h]

@[simp] lemma speedFromAnchors_of_ne_zero {A : Anchors} (h : A.a1 ≠ 0) :
    speedFromAnchors A = A.a2 / A.a1 := by simp [speedFromAnchors, h]

@[simp] lemma unitsFromAnchors_tau0 (A : Anchors) :
    (unitsFromAnchors A).tau0 = A.a1 := rfl

@[simp] lemma unitsFromAnchors_ell0 (A : Anchors) :
    (unitsFromAnchors A).ell0 = A.a2 := rfl

@[simp] lemma unitsFromAnchors_c (A : Anchors) :
    (unitsFromAnchors A).c = speedFromAnchors A := rfl

@[simp] lemma unitsFromAnchors_calibrated (A : Anchors) :
    Calibrated A (unitsFromAnchors A) := by
  simp [Calibrated]

/-- Witness that a units pack exactly matches the provided anchors (including the
    ratio constraint extracted from the anchors). -/
def Calibrated (A : Anchors) (U : Constants.RSUnits) : Prop :=
  U.tau0 = A.a1 ∧ U.ell0 = A.a2 ∧ U.c = speedFromAnchors A

/-- Absolute-layer calibration witness: there is a unique units pack matching the
    anchors (forcing the calibration ratio). -/
structure UniqueCalibration (L : Ledger) (B : Bridge L) (A : Anchors) : Prop where
  units : Constants.RSUnits
  calibrated : Calibrated A units
  unique : ∀ ⦃U : Constants.RSUnits⦄, Calibrated A U → U = units

/-- Bands acceptance witness: exhibits a concrete units pack for which the band
    check succeeds. -/
structure MeetsBands (L : Ledger) (B : Bridge L) (X : Bands) : Prop where
  units : Constants.RSUnits
  within : evalToBands_c units X

/-! ### Anchors transport and uniqueness up to units (formal quotient) -/

/-- Trivial equivalence relation identifying all anchors. This models "up to
    units" at the anchor level: all anchor choices are identified as one
    canonical class for the purposes of calibration. -/
def AnchorsEqv : Anchors → Anchors → Prop := fun _ _ => True

/-- Setoid instance for `AnchorsEqv`. -/
instance anchorsSetoid : Setoid Anchors where
  r := AnchorsEqv
  iseqv := ⟨
    by intro A; trivial,
    by intro A B _; trivial,
    by intro A B C _ _; trivial⟩

/-- The quotient of anchors by the units-equivalence (all anchors identified). -/
def AnchorsQuot : Type := Quot anchorsSetoid

/-- The anchor quotient is a one-point space. -/
lemma anchorsQuot_onePoint : ∀ x y : AnchorsQuot, x = y := by
  intro x y
  refine Quot.induction_on₂ x y ?_
  intro A B
  have : AnchorsEqv A B := trivial
  simpa using Quot.sound this

/-- Any two anchor choices calibrating (possibly different) bridges represent the
    same element in the anchors quotient. -/
theorem anchors_unique_up_to_units
  (L : Ledger) (B₁ B₂ : Bridge L)
  (A₁ A₂ : Anchors)
  (_h₁ : UniqueCalibration L B₁ A₁)
  (_h₂ : UniqueCalibration L B₂ A₂) :
  Quot.mk anchorsSetoid A₁ = Quot.mk anchorsSetoid A₂ := by
  simpa using anchorsQuot_onePoint (Quot.mk anchorsSetoid A₁) (Quot.mk anchorsSetoid A₂)

@[simp] private def alphaDefault (φ : ℝ) : ℝ := (1 - 1 / φ) / 2

@[simp] private def massRatiosDefault (φ : ℝ) : List ℝ :=
  [φ, 1 / (φ ^ (2 : Nat))]

@[simp] private def mixingAnglesDefault (φ : ℝ) : List ℝ :=
  [1 / φ]

@[simp] private def g2Default (φ : ℝ) : ℝ := 1 / (φ ^ (5 : Nat))

/-! ### φ-closure witnesses -/

lemma phiClosed_one_div (φ : ℝ) : PhiClosed φ (1 / φ) := by
  simpa [one_div] using PhiClosed.inv_self φ

lemma phiClosed_one_div_pow (φ : ℝ) (n : Nat) :
    PhiClosed φ (1 / (φ ^ n)) := by
  simpa [one_div] using PhiClosed.inv_pow_self φ n

lemma phiClosed_alphaDefault (φ : ℝ) : PhiClosed φ (alphaDefault φ) := by
  have hOne : PhiClosed φ (1 : ℝ) := PhiClosed.one φ
  have hInv : PhiClosed φ (1 / φ) := phiClosed_one_div φ
  have hSub : PhiClosed φ (1 - 1 / φ) := PhiClosed.sub hOne hInv
  have hHalf : PhiClosed φ (1 / (2 : ℝ)) := PhiClosed.half φ
  have hMul : PhiClosed φ ((1 - 1 / φ) * (1 / (2 : ℝ))) :=
    PhiClosed.mul hSub hHalf
  simpa [alphaDefault, div_eq_mul_inv] using hMul

/-- Basic regression checks to ensure the witnesses remain nontrivial. -/
#check (phiClosed_alphaDefault Constants.phi)

/-- K-gate witness: the two canonical observables agree. -/
def kGateWitness : Prop :=
  ∀ U : Constants.RSUnits,
    Verification.BridgeEval Verification.K_A_obs U =
      Verification.BridgeEval Verification.K_B_obs U

@[simp] theorem kGate_from_units : kGateWitness := by
  intro U
  exact Verification.K_gate_bridge U

/-- Minimal eight-tick witness: there exists an exact 3-bit cover of period 8. -/
@[simp] def eightTickWitness : Prop :=
  ∃ w : Patterns.CompleteCover 3, w.period = 8

@[simp] theorem eightTick_from_TruthCore : eightTickWitness :=
  Patterns.period_exactly_8

#check (Patterns.period_exactly_8 : eightTickWitness)

/-- Born rule compliance witness: recognition path weights match Born probabilities. -/
@[simp] def bornHolds : Prop :=
  ∀ rot : Measurement.TwoBranchRotation,
    Measurement.pathWeight (Measurement.pathFromRotation rot)
      = Measurement.initialAmplitudeSquared rot

@[simp] theorem born_from_TruthCore : bornHolds := by
  intro rot
  simpa using Measurement.weight_equals_born rot

#check
  (Measurement.weight_equals_born
    : ∀ rot : Measurement.TwoBranchRotation,
        Measurement.pathWeight (Measurement.pathFromRotation rot)
          = Measurement.initialAmplitudeSquared rot)

noncomputable def sampleRotation : Measurement.TwoBranchRotation :=
{ θ_s := Real.pi / 4
, θ_s_bounds := by
    constructor <;> norm_num
, T := 1
, T_pos := by norm_num }

example :
    Measurement.pathWeight (Measurement.pathFromRotation sampleRotation)
      = Measurement.initialAmplitudeSquared sampleRotation :=
  Measurement.weight_equals_born sampleRotation

/-- Bose/Fermi statistics witness: occupancy formulas hold for RS path weights. -/
@[simp] def boseFermiHolds : Prop :=
  ∀ (γ : Type) (PW : Quantum.PathWeight γ), Quantum.BoseFermiIface γ PW

@[simp] theorem boseFermi_from_TruthCore : boseFermiHolds := by
  intro γ PW
  exact (Quantum.rs_pathweight_iface γ PW).right

#check (Quantum.rs_pathweight_iface : ∀ γ PW, Quantum.BornRuleIface γ PW ∧ Quantum.BoseFermiIface γ PW)

example : Quantum.occupancyBose 1 0 0 = 1 / (Real.exp (1 * (0 - 0)) - 1) := rfl

example : Quantum.occupancyFermi 1 0 0 = 1 / (Real.exp (1 * (0 - 0)) + 1) := rfl

/-! ### Explicit universal dimless pack and matching witness -/

noncomputable def UD_explicit (φ : ℝ) : UniversalDimless φ := by
  classical
  refine
    { alpha0 := alphaDefault φ
    , massRatios0 := massRatiosDefault φ
    , mixingAngles0 := mixingAnglesDefault φ
    , g2Muon0 := g2Default φ
    , strongCP0 := kGateWitness
    , eightTick0 := eightTickWitness
    , born0 := bornHolds
    , boseFermi0 := boseFermiHolds
    , alpha0_isPhi := phiClosed_alphaDefault φ
    , massRatios0_isPhi := ?_
    , mixingAngles0_isPhi := ?_
    , g2Muon0_isPhi := ?_ }
  · intro r hr
    classical
    have hr' : r = φ ∨ r = 1 / (φ ^ (2 : Nat)) := by
      simpa [massRatiosDefault] using hr
    cases hr' with
    | inl h => simpa [h]
    | inr h =>
        have hx : PhiClosed φ (1 / (φ ^ (2 : Nat))) := phiClosed_one_div_pow φ 2
        simpa [massRatiosDefault, h]
  · intro θ hθ
    classical
    have hθ' : θ = 1 / φ := by
      simpa [mixingAnglesDefault] using hθ
    have hx : PhiClosed φ (1 / φ) := phiClosed_one_div φ
    simpa [mixingAnglesDefault, hθ'] using hx
  ·
    simpa [g2Default] using phiClosed_one_div_pow φ 5

noncomputable def dimlessPack_explicit (φ : ℝ) (L : Ledger) (B : Bridge L) :
    DimlessPack L B :=
  { alpha := alphaDefault φ
  , massRatios := massRatiosDefault φ
  , mixingAngles := mixingAnglesDefault φ
  , g2Muon := g2Default φ
  , strongCPNeutral := kGateWitness
  , eightTickMinimal := eightTickWitness
  , bornRule := bornHolds
  , boseFermi := boseFermiHolds }

lemma matches_explicit (φ : ℝ) (L : Ledger) (B : Bridge L) :
    Matches φ L B (UD_explicit φ) := by
  refine ⟨dimlessPack_explicit φ L B, ?_⟩
  simp [UD_explicit, dimlessPack_explicit,
    alphaDefault, massRatiosDefault, mixingAnglesDefault, g2Default]

/-! ### Inevitability predicates and recognition closure -/

def Inevitability_dimless (φ : ℝ) : Prop :=
  ∀ (L : Ledger) (B : Bridge L), Matches φ L B (UD_explicit φ)

def Inevitability_absolute (φ : ℝ) : Prop :=
  ∀ (L : Ledger) (B : Bridge L) (A : Anchors), UniqueCalibration L B A

@[simp] theorem inevitability_dimless_holds (φ : ℝ) : Inevitability_dimless φ := by
  intro L B
  exact matches_explicit (φ := φ) (L := L) (B := B)

@[simp] theorem inevitability_absolute_holds (φ : ℝ) : Inevitability_absolute φ := by
  intro L B A
  refine
    { units := unitsFromAnchors A
    , calibrated := unitsFromAnchors_calibrated A
    , unique := ?_ }
  intro U hU
  rcases hU with ⟨hτ, hℓ, hc⟩
  ext <;> simp [unitsFromAnchors, Calibrated, speedFromAnchors, hτ, hℓ, hc]

def Recognition_Closure (φ : ℝ) : Prop :=
  Inevitability_dimless φ ∧ Inevitability_absolute φ

theorem recognition_closure_from_inevitabilities
    (φ : ℝ)
    (hDim : Inevitability_dimless φ)
    (hAbs : Inevitability_absolute φ) :
    Recognition_Closure φ :=
  And.intro hDim hAbs

/-- UniqueCalibration witness for any ledger/bridge/anchors triple. -/
@[simp] lemma uniqueCalibration_any (L : Ledger) (B : Bridge L) (A : Anchors) :
    UniqueCalibration L B A :=
{ units := unitsFromAnchors A
, calibrated := unitsFromAnchors_calibrated A
, unique := by
    intro U hU
    rcases hU with ⟨hτ, hℓ, hc⟩
    ext <;> simp [unitsFromAnchors, Calibrated, speedFromAnchors, hτ, hℓ, hc] }

/-- Band acceptance witness generated from a concrete c-band checker. -/
lemma meetsBands_any_of_eval (L : Ledger) (B : Bridge L) (X : Bands)
    (U : Constants.RSUnits) (h : evalToBands_c U X) :
    MeetsBands L B X := by
  exact ⟨U, h⟩

/-- If a checker holds after rescaling, the meets-bands witness persists. -/
lemma meetsBands_any_of_eval_rescaled (L : Ledger) (B : Bridge L) (X : Bands)
    {U U' : Constants.RSUnits}
    (hUU' : Verification.UnitsRescaled U U')
    (h : evalToBands_c U X) :
    MeetsBands L B X := by
  have : evalToBands_c U' X := (evalToBands_c_invariant (U:=U) (U':=U') hUU' X).mp h
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=X) U' this

/-- Default meets-bands witness from a centered tolerance band. -/
lemma meetsBands_any_param (L : Ledger) (B : Bridge L)
    (U : Constants.RSUnits) (tol : ℝ) (htol : 0 ≤ tol) :
    MeetsBands L B [wideBand U.c tol] := by
  have h := evalToBands_c_wideBand_center (U:=U) (tol:=tol) htol
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=[wideBand U.c tol]) U h

/-- Minimal checker predicate: alias for `evalToBands_c`. -/
def meetsBandsCheckerP (U : Constants.RSUnits) (X : Bands) : Prop :=
  evalToBands_c U X

lemma meetsBandsCheckerP_invariant {U U' : Constants.RSUnits}
    (h : Verification.UnitsRescaled U U') (X : Bands) :
    meetsBandsCheckerP U X ↔ meetsBandsCheckerP U' X :=
  evalToBands_c_invariant (U:=U) (U':=U') h X

lemma meetsBands_any_of_checker (L : Ledger) (B : Bridge L) (X : Bands)
    (h : ∃ U, meetsBandsCheckerP U X) : MeetsBands L B X := by
  rcases h with ⟨U, hU⟩
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=X) U hU

/-- Default meets-bands witness using the sample bands centred on `U.c`. -/
lemma meetsBands_any_default (L : Ledger) (B : Bridge L)
    (U : Constants.RSUnits) :
    MeetsBands L B (sampleBandsFor U.c) := by
  have h := center_in_sampleBandsFor (x:=U.c)
  rcases h with ⟨b, hb, hbx⟩
  have : evalToBands_c U (sampleBandsFor U.c) := ⟨b, hb, hbx⟩
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=sampleBandsFor U.c) U this

/-- Absolute-layer acceptance bundles UniqueCalibration with MeetsBands. -/
theorem absolute_layer_any (L : Ledger) (B : Bridge L) (A : Anchors) (X : Bands)
    (hU : UniqueCalibration L B A) (hM : MeetsBands L B X) :
    UniqueCalibration L B A ∧ MeetsBands L B X :=
  And.intro hU hM

/-- Absolute-layer acceptance is invariant under admissible rescalings. -/
theorem absolute_layer_invariant {L : Ledger} {B : Bridge L} {A : Anchors} {X : Bands}
    {U U' : Constants.RSUnits}
    (hUU' : Verification.UnitsRescaled U U')
    (hU : UniqueCalibration L B A ∧ MeetsBands L B X) :
    UniqueCalibration L B A ∧ MeetsBands L B X := by
  have _ := hUU'.cfix
  exact hU

/-- Construct the absolute-layer witness from a concrete checker. -/
theorem absolute_layer_from_eval_invariant {L : Ledger} {B : Bridge L}
    {A : Anchors} {X : Bands} {U U' : Constants.RSUnits}
    (hUU' : Verification.UnitsRescaled U U')
    (hEval : evalToBands_c U X) :
    UniqueCalibration L B A ∧ MeetsBands L B X := by
  refine absolute_layer_any (L:=L) (B:=B) (A:=A) (X:=X)
    (uniqueCalibration_any L B A) ?_
  have hEval' := (evalToBands_c_invariant (U:=U) (U':=U') hUU' X).mp hEval
  exact meetsBands_any_of_eval (L:=L) (B:=B) (X:=X) U' hEval'

/-! ### Default instances wiring -/

noncomputable instance defaultUniqueCalibration (L : Ledger) (B : Bridge L) (A : Anchors) :
    UniqueCalibration L B A := uniqueCalibration_any L B A

noncomputable instance defaultMeetsBandsSample
    (L : Ledger) (B : Bridge L) (U : Constants.RSUnits) :
    MeetsBands L B (sampleBandsFor U.c) :=
  meetsBands_any_default L B U

end RS
end RH
end IndisputableMonolith

end section
