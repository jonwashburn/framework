import Mathlib
import IndisputableMonolith.Verification

namespace IndisputableMonolith
namespace RH
namespace RS

structure Band where
  lo : ℝ
  hi : ℝ

def Band.width (b : Band) : ℝ := b.hi - b.lo

abbrev Bands := List Band

def Band.contains (b : Band) (x : ℝ) : Prop := b.lo ≤ x ∧ x ≤ b.hi

def Band.Valid (b : Band) : Prop := b.lo ≤ b.hi

lemma Band.contains_lo_of_valid (b : Band) (hb : Band.Valid b) :
  Band.contains b b.lo := by
  dsimp [Band.contains, Band.Valid] at *
  exact And.intro le_rfl hb

lemma Band.contains_hi_of_valid (b : Band) (hb : Band.Valid b) :
  Band.contains b b.hi := by
  dsimp [Band.contains, Band.Valid] at *
  exact And.intro hb le_rfl

lemma Band.width_nonneg (b : Band) (hb : Band.Valid b) : 0 ≤ b.width := by
  dsimp [Band.width, Band.Valid] at *
  exact sub_nonneg.mpr hb

def wideBand (x : ℝ) (ε : ℝ) : Band := { lo := x - ε, hi := x + ε }

lemma wideBand_width {x ε : ℝ} (hε : 0 ≤ ε) : (wideBand x ε).width = 2 * ε := by
  dsimp [Band.width, wideBand]
  ring

lemma wideBand_width_nonneg {x ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ (wideBand x ε).width := by
  have hw : (wideBand x ε).width = 2 * ε := wideBand_width (x:=x) (ε:=ε) hε
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hnonneg : 0 ≤ 2 * ε := mul_nonneg h2 hε
  simpa [hw] using hnonneg

lemma wideBand_contains_center {x ε : ℝ} (hε : 0 ≤ ε) :
  Band.contains (wideBand x ε) x := by
  dsimp [Band.contains, wideBand]
  constructor
  · have : x - ε ≤ x := by simpa using sub_le_self x hε
    simpa using this
  ·
    have hx : x ≤ x + ε := by
      have : x + 0 ≤ x + ε := add_le_add_left hε x
      simpa [zero_add] using this
    simpa using hx

lemma wideBand_valid {x ε : ℝ} (hε : 0 ≤ ε) : (wideBand x ε).Valid := by
  dsimp [Band.Valid, wideBand]
  linarith

lemma wideBand_contains_lo {x ε : ℝ} (hε : 0 ≤ ε) :
  Band.contains (wideBand x ε) (wideBand x ε).lo :=
  Band.contains_lo_of_valid _ (wideBand_valid (x:=x) (ε:=ε) hε)

lemma wideBand_contains_hi {x ε : ℝ} (hε : 0 ≤ ε) :
  Band.contains (wideBand x ε) (wideBand x ε).hi :=
  Band.contains_hi_of_valid _ (wideBand_valid (x:=x) (ε:=ε) hε)

@[simp] def sampleBandsFor (x : ℝ) : Bands := [wideBand x 1]

lemma sampleBandsFor_nonempty (x : ℝ) : (sampleBandsFor x).length = 1 := by
  simp [sampleBandsFor]

lemma sampleBandsFor_singleton (x : ℝ) : sampleBandsFor x = [wideBand x 1] := by
  simp [sampleBandsFor]

@[simp] def evalBandsAt (c : ℝ) (x : ℝ) : Bands := sampleBandsFor (c * x)

noncomputable def meetsBandsChecker_gen (xs : List ℝ) (bs : Bands) : Bool := by
  classical
  exact xs.any (fun x => bs.any (fun b => decide (Band.contains b x)))

noncomputable def meetsBandsChecker (xs : List ℝ) (c : ℝ) : Bool :=
  meetsBandsChecker_gen xs (evalBandsAt c 1)

/-- Evaluate whether the anchors `U.c` lie in any of the candidate bands `X`. -/
def evalToBands_c (U : IndisputableMonolith.Constants.RSUnits) (X : Bands) : Prop :=
  ∃ b ∈ X, Band.contains b U.c

/-- Invariance of the c-band check under units rescaling (c fixed by cfix). -/
lemma evalToBands_c_invariant {U U' : IndisputableMonolith.Constants.RSUnits}
  (h : IndisputableMonolith.Verification.UnitsRescaled U U') (X : Bands) :
  evalToBands_c U X ↔ evalToBands_c U' X := by
  dsimp [evalToBands_c]
  have hc : U'.c = U.c := h.cfix
  constructor
  · intro hx
    rcases hx with ⟨b, hb, hbx⟩
    refine ⟨b, hb, ?_⟩
    simpa [Band.contains, hc] using hbx
  · intro hx
    rcases hx with ⟨b, hb, hbx⟩
    refine ⟨b, hb, ?_⟩
    simpa [Band.contains, hc.symm] using hbx

/-- The centered `wideBand` around `U.c` always includes `U.c`. -/
lemma evalToBands_c_wideBand_center
  (U : IndisputableMonolith.Constants.RSUnits) (tol : ℝ) (htol : 0 ≤ tol) :
  evalToBands_c U [wideBand U.c tol] := by
  refine ⟨wideBand U.c tol, by simp, ?_⟩
  simpa using wideBand_contains_center (x:=U.c) (ε:=tol) htol

/-- Convenience: `sampleBandsFor x` contains `x`, hence satisfies `evalToBands_c` with anchors `c=x`. -/
lemma evalToBands_c_sampleBandsFor
  (x : ℝ) : evalToBands_c { tau0 := 1, ell0 := x, c := x, c_ell0_tau0 := by simp } (sampleBandsFor x) := by
  refine ⟨wideBand x 1, ?_, ?_⟩
  · simp [sampleBandsFor]
  · simpa using wideBand_contains_center (x:=x) (ε:=1) (by norm_num)

@[simp] lemma meetsBandsChecker_gen_nil (bs : Bands) :
  meetsBandsChecker_gen [] bs = false := by
  classical
  simp [meetsBandsChecker_gen]

@[simp] lemma meetsBandsChecker_nil (c : ℝ) :
  meetsBandsChecker [] c = false := by
  classical
  simp [meetsBandsChecker, meetsBandsChecker_gen]

@[simp] lemma meetsBandsChecker_gen_nilBands (xs : List ℝ) :
  meetsBandsChecker_gen xs [] = false := by
  classical
  simp [meetsBandsChecker_gen]

lemma center_in_sampleBandsFor (x : ℝ) :
  ∃ b ∈ sampleBandsFor x, Band.contains b x := by
  refine ⟨wideBand x 1, ?_, ?_⟩
  · simp [sampleBandsFor]
  · have : Band.contains (wideBand x 1) x := wideBand_contains_center (x:=x) (ε:=1) (by norm_num)
    simpa using this

lemma center_in_each_sample (x : ℝ) :
  ∀ {b}, b ∈ sampleBandsFor x → Band.contains b x := by
  intro b hb
  have hb' : b = wideBand x 1 := by
    simpa [sampleBandsFor] using hb
  simpa [hb'] using wideBand_contains_center (x:=x) (ε:=1) (by norm_num)

end RS
end RH
end IndisputableMonolith
