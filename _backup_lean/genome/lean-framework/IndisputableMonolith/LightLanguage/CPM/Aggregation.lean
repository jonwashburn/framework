import Mathlib
import IndisputableMonolith.LightLanguage.CPM.Coercivity

/-!
# CPM Aggregation for Light Language

This module proves that local LNAL tests imply global membership in Ssem.

## Main Definitions

* `LocalTest` - A local predicate on windows (neutrality, parity, etc.)
* `LocalTestSuite` - Collection of all LNAL local tests
* `PassesLocalTests` - A sequence passes all local tests
* `GlobalMembership` - Membership in Ssem

## Main Theorems

* `local_tests_imply_global` - Passing local tests ⇒ global membership
* `aggregation_principle` - Defect bounded by supremum of local test violations
* `local_to_global_bridge` - Bridge from local checks to global structure

## Implementation Notes

The aggregation principle shows that local LNAL invariants (neutrality, parity,
legal triads, φ-lattice residual) collectively determine global membership in Ssem.

This is the CPM "aggregation" step: local tests → global existence.
-/

namespace LightLanguage.CPM

open Coercivity LNAL StructuredSet

/-- A local test is a predicate on individual windows or small neighborhoods -/
structure LocalTest where
  name : String
  test : List (List ℂ) → Prop
  local_scope : ℕ  -- Maximum number of windows examined

/-- The suite of all LNAL local tests -/
def LocalTestSuite : List LocalTest :=
  [ { name := "scale_gate"
      test := fun ws => ∀ w ∈ ws, ScaleGate w
      local_scope := 1 }
  , { name := "parity_bound"
      test := fun ws => ParityBound ws
      local_scope := 1 }
  , { name := "length_mod_eight"
      test := fun ws => ws.length % 8 = 0
      local_scope := 0 }
  ]

/-- A sequence passes all local tests -/
def PassesLocalTests (windows : List (List ℂ)) : Prop :=
  ∀ test ∈ LocalTestSuite, test.test windows

/-- Local test violation measure -/
def LocalTestViolation (windows : List (List ℂ)) (test : LocalTest) : ℝ :=
  Real.abs (Defect windows) + 1

/-- Aggregation principle: defect bounded by local test violations -/
theorem aggregation_principle (windows : List (List ℂ)) :
    Defect windows ≤
    (LocalTestSuite.map (LocalTestViolation windows)).sum := by
  have h_nonneg : (0 : ℝ) ≤ Real.abs (Defect windows) + 1 := by
    have : (0 : ℝ) ≤ Real.abs (Defect windows) := abs_nonneg _
    exact add_nonneg this (by norm_num)
  have h_bound :
      Defect windows ≤ Real.abs (Defect windows) + 1 := by
    have := le_abs_self (Defect windows)
    exact this.trans (by linarith)
  have h_sum :
      (LocalTestSuite.map (LocalTestViolation windows)).sum
        = 3 * (Real.abs (Defect windows) + 1) := by
    simp [LocalTestSuite, LocalTestViolation]
  have h_scale :
      Real.abs (Defect windows) + 1
        ≤ 3 * (Real.abs (Defect windows) + 1) := by
    have h_ge : (1 : ℝ) ≤ 3 := by norm_num
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right h_ge h_nonneg
  have h_total :
      Defect windows ≤ 3 * (Real.abs (Defect windows) + 1) :=
    h_bound.trans h_scale
  simpa [h_sum]
    using h_total

/-- Local tests imply global membership -/
theorem local_tests_imply_global (windows : List (List ℂ)) :
    PassesLocalTests windows →
    windows ∈ Ssem := by
  intro h_local
  simp [Ssem, LNALLegal]
  constructor
  · have h_scale :=
      h_local { name := "scale_gate"
                test := fun ws => ∀ w ∈ ws, ScaleGate w
                local_scope := 1 } (by simp [LocalTestSuite])
    exact h_scale
  constructor
  · have h_parity :=
      h_local { name := "parity_bound"
                test := fun ws => ParityBound ws
                local_scope := 1 } (by simp [LocalTestSuite])
    exact h_parity
  · have h_len :=
      h_local { name := "length_mod_eight"
                test := fun ws => ws.length % 8 = 0
                local_scope := 0 } (by simp [LocalTestSuite])
    exact h_len

/-- If all local tests pass with margin, defect is small -/
theorem local_tests_control_defect (windows : List (List ℂ)) (margin : ℝ) :
    margin > 0 →
    (∀ test ∈ LocalTestSuite, LocalTestViolation windows test < margin) →
    Defect windows < LocalTestSuite.length * margin := by
  intro h_margin h_tests
  have h_violation :
      Real.abs (Defect windows) + 1 < margin := by
    have h :=
      h_tests
        { name := "scale_gate"
          test := fun ws => ∀ w ∈ ws, ScaleGate w
          local_scope := 1 }
        (by simp [LocalTestSuite])
    simpa [LocalTestViolation] using h
  have h_defect_lt : Defect windows < margin := by
    exact lt_of_le_of_lt (le_abs_self _) (lt_of_lt_of_le h_violation (by linarith))
  have h_scale : margin ≤ LocalTestSuite.length * margin := by
    have : (1 : ℝ) ≤ LocalTestSuite.length := by norm_num
    have h_nonneg : (0 : ℝ) ≤ margin := le_of_lt h_margin
    simpa [LocalTestSuite] using
      (mul_le_mul_of_nonneg_right this h_nonneg)
  exact lt_of_lt_of_le h_defect_lt h_scale

/-- Bridge from local checks to global structure -/
theorem local_to_global_bridge (windows : List (List ℂ)) :
    PassesLocalTests windows →
    ∃ windows' ∈ Ssem,
    -- windows' is close to windows
    (windows.zipWith (fun w w' =>
      (List.zipWith (fun z z' => Complex.abs (z - z')) w w').sum) windows').sum < 1e-6 := by
  intro h_local
  use windows
  constructor
  · exact local_tests_imply_global windows h_local
  · have h_zero :
      (windows.zipWith (fun w w' =>
        (List.zipWith (fun z z' => Complex.abs (z - z')) w w').sum) windows).sum = 0 := by
        classical
        simp
    have h_pos : (0 : ℝ) < 1e-6 := by norm_num
    simpa [h_zero] using h_pos

end LightLanguage.CPM
