import Mathlib
import IndisputableMonolith.URCGenerators
import IndisputableMonolith.Verification.Dimension
import IndisputableMonolith.Patterns.CompleteCover
import IndisputableMonolith.Verification.DimensionCRT
import IndisputableMonolith.Constants
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.Verification.Exclusivity
import IndisputableMonolith.Verification.Completeness
import IndisputableMonolith.Verification.RecognitionReality

namespace IndisputableMonolith.URCAdapters.Reports

open IndisputableMonolith.URCGenerators

/-- #eval-friendly uniqueness check for the RS framework. -/
def framework_uniqueness_report : String :=
  let φ : ℝ := IndisputableMonolith.Constants.phi
  have _ : IndisputableMonolith.RecogSpec.FrameworkUniqueness φ :=
    IndisputableMonolith.RecogSpec.framework_uniqueness φ
  "FrameworkUniqueness: OK"

/-- #eval-friendly arithmetic-only check: lcm(2^D,45)=360 iff D=3. -/
def dimensional_rigidity_lite_report : String :=
  let D3 : Nat := 3
  have h : Nat.lcm (2 ^ D3) 45 = 360 := by decide
  have _ : D3 = 3 := (IndisputableMonolith.Verification.DimensionCRT.lcm_pow2_45_eq_360_iff D3).mp h
  "DimensionalRigidity-lite: OK"

/-- #eval-friendly dimensional rigidity report under the combined RSCounting+Gap45+Absolute witness. -/
def dimensional_rigidity_report : String :=
  let D3 : Nat := 3
  -- Provide the coverage and synchronization witnesses for D=3
  have hcov : ∃ w : IndisputableMonolith.Patterns.CompleteCover D3, w.period = 2 ^ D3 :=
    IndisputableMonolith.Patterns.cover_exact_pow D3
  have hsync : Nat.lcm (2 ^ D3) 45 = 360 := by decide
  have _ : D3 = 3 :=
    IndisputableMonolith.Verification.Dimension.onlyD3_satisfies_RSCounting_Gap45_Absolute
      (And.intro hcov (And.intro hsync (EightTickMinimalCert.verified_any {})))

  "DimensionalRigidity: OK"

/-- #eval-friendly report asserting exactly three generations via a surjective index. -/
def generations_count_report : String :=
  let cert : URCGenerators.GenerationCountCert := {}
  have _ : URCGenerators.GenerationCountCert.verified cert :=
    URCGenerators.GenerationCountCert.verified_any _
  "GenerationsCount: OK (exactly three)"

/-- #eval-friendly report for the exact‑3 generations bundle tying equal‑Z,
    rung laws, and residue/anchor policies to the generation index. -/
def exact_three_generations_report : String :=
  let cert : URCGenerators.ExactThreeGenerationsCert := {}
  have _ : URCGenerators.ExactThreeGenerationsCert.verified cert :=
    URCGenerators.ExactThreeGenerationsCert.verified_any _
  "ExactThreeGenerations: OK"

/-- #eval-friendly report for the upper bound (≤3 generations). -/
def generations_upper_bound_report : String :=
  let cert : URCGenerators.GenUpperBoundCert := {}
  have _ : URCGenerators.GenUpperBoundCert.verified cert :=
    URCGenerators.GenUpperBoundCert.verified_any _
  "GenerationsUpperBound (≤3): OK"

/-- #eval-friendly report for the lower bound (≥3 generations). -/
def generations_lower_bound_report : String :=
  let cert : URCGenerators.GenLowerBoundCert := {}
  have _ : URCGenerators.GenLowerBoundCert.verified cert :=
    URCGenerators.GenLowerBoundCert.verified_any _
  "GenerationsLowerBound (≥3): OK"

end IndisputableMonolith.URCAdapters.Reports
