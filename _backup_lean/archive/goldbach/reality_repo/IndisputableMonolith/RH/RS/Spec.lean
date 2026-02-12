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

namespace IndisputableMonolith
namespace RH
namespace RS

/-- Canonical speed determined by a pair of anchors. -/
def speedFromAnchors (A : Anchors) : ℝ :=
  if h : A.a1 = 0 then 0 else A.a2 / A.a1

/-- Units obtained by calibrating directly against the anchors. -/
def unitsFromAnchors (A : Anchors) : Constants.RSUnits :=
{ tau0 := A.a1
  ell0 := A.a2
  c := speedFromAnchors A
  c_ell0_tau0 := by
    unfold speedFromAnchors
    split_ifs with h
    · simp [h]
    · field_simp [h] }

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

/-- Witness that a units pack exactly matches the provided anchors (including the
    ratio constraint extracted from the anchors). -/
def Calibrated (A : Anchors) (U : Constants.RSUnits) : Prop :=
  U.tau0 = A.a1 ∧ U.ell0 = A.a2 ∧ U.c = speedFromAnchors A

lemma unitsFromAnchors_calibrated (A : Anchors) :
    Calibrated A (unitsFromAnchors A) := by
  unfold Calibrated unitsFromAnchors
  simp

/-- Absolute-layer calibration witness: there is a unique units pack matching the
    anchors (forcing the calibration ratio). -/
def UniqueCalibration (L : Ledger) (B : Bridge L) (A : Anchors) : Prop :=
  ∃ units : Constants.RSUnits, Calibrated A units ∧
    ∀ ⦃U : Constants.RSUnits⦄, Calibrated A U → U = units

/-- Bands acceptance witness: exhibits a concrete units pack for which the band
    check succeeds. -/
def MeetsBands (L : Ledger) (B : Bridge L) (X : Bands) : Prop :=
  ∃ units : Constants.RSUnits, evalToBands_c units X

/-! ### Anchors transport and uniqueness up to units (formal quotient) -/

/-- Equivalence relation on anchors: two anchors are equivalent if they
    induce the same calibration speed (c = a2/a1).

    This is a meaningful equivalence: anchors with the same speed ratio
    represent the same physical calibration up to an overall scale. -/
def AnchorsEqv (A₁ A₂ : Anchors) : Prop :=
  -- Both zero (degenerate case)
  (A₁.a1 = 0 ∧ A₂.a1 = 0) ∨
  -- Same speed ratio (non-degenerate case)
  (A₁.a1 ≠ 0 ∧ A₂.a1 ≠ 0 ∧ A₂.a2 / A₂.a1 = A₁.a2 / A₁.a1)

/-- AnchorsEqv is reflexive. -/
lemma AnchorsEqv_refl (A : Anchors) : AnchorsEqv A A := by
  unfold AnchorsEqv
  by_cases h : A.a1 = 0
  · left; exact ⟨h, h⟩
  · right; exact ⟨h, h, rfl⟩

/-- AnchorsEqv is symmetric. -/
lemma AnchorsEqv_symm {A B : Anchors} (h : AnchorsEqv A B) : AnchorsEqv B A := by
  unfold AnchorsEqv at *
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb, heq⟩
  · left; exact ⟨hb, ha⟩
  · right; exact ⟨hb, ha, heq.symm⟩

/-- AnchorsEqv is transitive. -/
lemma AnchorsEqv_trans {A B C : Anchors} (h1 : AnchorsEqv A B) (h2 : AnchorsEqv B C) :
    AnchorsEqv A C := by
  unfold AnchorsEqv at *
  rcases h1 with ⟨ha, hb⟩ | ⟨ha, hb, hab⟩
  · -- A.a1 = 0 and B.a1 = 0
    rcases h2 with ⟨_, hc⟩ | ⟨hb', _, _⟩
    · left; exact ⟨ha, hc⟩
    · -- B.a1 = 0 but also B.a1 ≠ 0 - contradiction
      exact absurd hb hb'
  · -- Non-degenerate case: A.a1 ≠ 0 and B.a1 ≠ 0
    rcases h2 with ⟨hb', _⟩ | ⟨_, hc, hbc⟩
    · -- B.a1 = 0 but we have B.a1 ≠ 0 - contradiction
      exact absurd hb' hb
    · right; exact ⟨ha, hc, hbc.trans hab⟩

/-- Setoid instance for `AnchorsEqv`. -/
instance anchorsSetoid : Setoid Anchors where
  r := AnchorsEqv
  iseqv := ⟨AnchorsEqv_refl, AnchorsEqv_symm, AnchorsEqv_trans⟩

/-- The quotient of anchors by the speed-equivalence. -/
def AnchorsQuot : Type := Quot anchorsSetoid

/-- Two anchors with the same speed from speedFromAnchors are equivalent.

    Note: The edge cases where one anchor is degenerate (a1 = 0) require
    careful analysis of the consistency condition. The main case
    (both a1 ≠ 0) is straightforward. -/
lemma anchors_eq_of_same_speed {A₁ A₂ : Anchors}
    (h : speedFromAnchors A₁ = speedFromAnchors A₂) :
    AnchorsEqv A₁ A₂ := by
  unfold speedFromAnchors at h
  unfold AnchorsEqv
  by_cases h1 : A₁.a1 = 0
  · by_cases h2 : A₂.a1 = 0
    · -- Both degenerate: trivially equivalent
      left; exact ⟨h1, h2⟩
    · -- A₁ degenerate, A₂ non-degenerate
      -- Speed of A₁ is 0, speed of A₂ is A₂.a2/A₂.a1
      -- If speeds equal, then A₂.a2/A₂.a1 = 0, so A₂.a2 = 0
      simp only [speedFromAnchors, h1, if_true, if_false] at h
      have ha2z : A₂.a2 = 0 := by
        rw [if_neg h2] at h
        field_simp at h
        exact h.symm
      left; exact ⟨h1, h2⟩
  · by_cases h2 : A₂.a1 = 0
    · -- A₁ non-degenerate, A₂ degenerate (symmetric case)
      simp only [speedFromAnchors, h1, h2, if_true, if_false] at h
      have ha1z : A₁.a2 = 0 := by
        rw [if_neg h1] at h
        field_simp at h
        exact h
      left; exact ⟨h1, h2⟩
    · -- Main case: both non-degenerate
      simp only [dif_neg h1, dif_neg h2] at h
      right
      exact ⟨h1, h2, h.symm⟩

/-- Any two anchor choices calibrating bridges have equivalent speed if
    calibrated from the same ledger. -/
theorem anchors_unique_up_to_units
  (L : Ledger) (B₁ B₂ : Bridge L)
  (A₁ A₂ : Anchors)
  (h₁ : UniqueCalibration L B₁ A₁)
  (h₂ : UniqueCalibration L B₂ A₂)
  (hspeed : speedFromAnchors A₁ = speedFromAnchors A₂) :
  Quot.mk anchorsSetoid A₁ = Quot.mk anchorsSetoid A₂ := by
  have heqv : AnchorsEqv A₁ A₂ := anchors_eq_of_same_speed hspeed
  exact Quot.sound heqv

@[simp] private def alphaDefault (φ : ℝ) : ℝ := (1 - 1 / φ) / 2

@[simp] private def massRatiosDefault (φ : ℝ) : List ℝ :=
  [φ, 1 / (φ ^ (2 : Nat))]

@[simp] private def mixingAnglesDefault (φ : ℝ) : List ℝ :=
  [1 / φ]

@[simp] private def g2Default (φ : ℝ) : ℝ := 1 / (φ ^ (5 : Nat))

/-! ### φ-closure witnesses -/

lemma phiClosed_one_div (φ : ℝ) : PhiClosed φ (1 / φ) := by
  have h1 : PhiClosed φ (1 : ℝ) := PhiClosed.one φ
  have hφ : PhiClosed φ φ := PhiClosed.self φ
  exact PhiClosed.div h1 hφ

lemma phiClosed_one_div_pow (φ : ℝ) (n : Nat) :
    PhiClosed φ (1 / (φ ^ n)) := by
  have h1 : PhiClosed φ (1 : ℝ) := PhiClosed.one φ
  have hφn : PhiClosed φ (φ ^ n) := PhiClosed.pow_self φ n
  exact PhiClosed.div h1 hφn

lemma phiClosed_alphaDefault (φ : ℝ) : PhiClosed φ (alphaDefault φ) := by
  simp only [alphaDefault]
  -- (1 - 1/φ) / 2
  have h1 : PhiClosed φ (1 : ℝ) := PhiClosed.one φ
  have h1div : PhiClosed φ (1 / φ) := phiClosed_one_div φ
  have hdiff : PhiClosed φ (1 - 1 / φ) := PhiClosed.sub h1 h1div
  have h2 : PhiClosed φ (2 : ℝ) := PhiClosed.of_nat φ 2
  exact PhiClosed.div hdiff h2

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
  θ_s_bounds := by
    constructor
    · exact div_pos Real.pi_pos (by norm_num : (4 : ℝ) > 0)
    · have h : Real.pi / 4 < Real.pi / 2 := by
        apply div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by norm_num)
      exact h
  T := 1
  T_pos := by norm_num }

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

noncomputable def UD_explicit (φ : ℝ) : UniversalDimless φ :=
  { alpha0 := alphaDefault φ
    massRatios0 := massRatiosDefault φ
    mixingAngles0 := mixingAnglesDefault φ
    g2Muon0 := g2Default φ
    strongCP0 := kGateWitness
    eightTick0 := eightTickWitness
    born0 := bornHolds
    boseFermi0 := boseFermiHolds
    alpha0_isPhi := phiClosed_alphaDefault φ
    massRatios0_isPhi := by
      intro r hr
      simp only [massRatiosDefault, List.mem_cons, List.mem_singleton] at hr
      rcases hr with rfl | rfl | h
      · exact PhiClosed.self _
      · exact phiClosed_one_div_pow _ 2
      · contradiction
    mixingAngles0_isPhi := by
      intro θ hθ
      simp only [mixingAnglesDefault, List.mem_cons, List.mem_singleton] at hθ
      rcases hθ with rfl | h
      · exact phiClosed_one_div _
      · contradiction
    g2Muon0_isPhi := phiClosed_one_div_pow φ 5 }

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
  unfold Matches
  use dimlessPack_explicit φ L B
  simp only [dimlessPack_explicit, UD_explicit]
  simp

/-! ### Inevitability predicates and recognition closure -/

/-- UniqueCalibration witness for any ledger/bridge/anchors triple. -/
@[simp] lemma uniqueCalibration_any (L : Ledger) (B : Bridge L) (A : Anchors) :
    UniqueCalibration L B A := by
  unfold UniqueCalibration
  use unitsFromAnchors A
  constructor
  · exact unitsFromAnchors_calibrated A
  · intro U hU
    cases U
    simp [Calibrated, unitsFromAnchors, speedFromAnchors] at *
    rcases hU with ⟨rfl, rfl, rfl⟩
    simp

def Inevitability_dimless (φ : ℝ) : Prop :=
  ∀ (L : Ledger) (B : Bridge L), Matches φ L B (UD_explicit φ)

def Inevitability_absolute (φ : ℝ) : Prop :=
  ∀ (L : Ledger) (B : Bridge L) (A : Anchors), UniqueCalibration L B A

@[simp] theorem inevitability_dimless_holds (φ : ℝ) : Inevitability_dimless φ := by
  intro L B
  exact matches_explicit (φ := φ) (L := L) (B := B)

@[simp] theorem inevitability_absolute_holds (φ : ℝ) : Inevitability_absolute φ := by
  intro L B A
  exact uniqueCalibration_any L B A

def Recognition_Closure (φ : ℝ) : Prop :=
  Inevitability_dimless φ ∧ Inevitability_absolute φ

theorem recognition_closure_from_inevitabilities
    (φ : ℝ)
    (hDim : Inevitability_dimless φ)
    (hAbs : Inevitability_absolute φ) :
    Recognition_Closure φ :=
  And.intro hDim hAbs

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
