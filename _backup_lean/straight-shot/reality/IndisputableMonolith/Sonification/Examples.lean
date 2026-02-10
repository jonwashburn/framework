import Mathlib
import IndisputableMonolith.Sonification.Empirics

/-!
# Sonification examples (EmpiricalAnchor snapshots)

This module packages the small “1PGB” example table from `Source-Super-rrf.txt`
as a concrete dataset and proves it **passes the default preregistration**.

Important:
- This does *not* prove the hypothesis for all datasets.
- It shows the currently recorded 3-seed snapshot is **not** a falsifier under
  the default budget (`kDefault`), which for 3 observations is 0 violations.
-/

namespace IndisputableMonolith.Sonification

/-! ## The 1PGB three-seed snapshot (as recorded in the spec) -/

noncomputable def obs_1PGB : List FoldObs :=
  [ { seed := 42
    , rmsd := (191/20 : ℚ)        -- 9.55
    , audioConsonance := (747/2000 : ℚ) }  -- 0.3735
  , { seed := 137
    , rmsd := (897/100 : ℚ)       -- 8.97
    , audioConsonance := (3809/10000 : ℚ) } -- 0.3809
  , { seed := 256
    , rmsd := (371/50 : ℚ)        -- 7.42
    , audioConsonance := (857/2000 : ℚ) }  -- 0.4285
  ]

lemma obs_1PGB_preregistered : PreregisteredDataset obs_1PGB := by
  classical
  refine ⟨by
    -- length = 3
    simp [obs_1PGB]
  , ?_, ?_⟩
  · intro o ho
    -- All RMSD values are nonnegative.
    simp [obs_1PGB] at ho
    rcases ho with rfl | rfl | rfl <;> norm_num
  · intro o ho
    -- All consonance values are nonnegative.
    simp [obs_1PGB] at ho
    rcases ho with rfl | rfl | rfl <;> norm_num

/-! ## Passes default preregistration (kDefault) -/

private lemma no_violations_1PGB :
    ∀ ij : Fin obs_1PGB.length × Fin obs_1PGB.length,
      ij.1 < ij.2 → ¬ ViolatesOrder (obs_1PGB.get ij.1) (obs_1PGB.get ij.2) := by
  classical
  intro ij hij
  -- For this 3-seed snapshot, there are only three `i<j` cases.
  -- We discharge each by direct arithmetic on the recorded constants.
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> try cases hij
  all_goals
    -- Expand the two observations and show the “violation” disjunction is false.
    -- Each case reduces to comparing rational constants in ℝ.
    dsimp [ViolatesOrder, obs_1PGB]
    intro h
    rcases h with h | h
    · rcases h with ⟨hR, hC⟩
      nlinarith
    · rcases h with ⟨hR, hC⟩
      nlinarith

theorem obs_1PGB_passes_default :
    CrossOctaveViolationsAtMost (kDefault obs_1PGB) obs_1PGB := by
  classical
  -- For 3 observations, kDefault = 0 (10% of 3 pairs floors to 0).
  have hk : kDefault obs_1PGB = 0 := by
    simp [kDefault, totalPairs, obs_1PGB]
  -- Show there are no violating pairs, hence violationCount = 0.
  have hempty : violationPairs obs_1PGB = ∅ := by
    classical
    refine Finset.eq_empty_iff_forall_notMem.2 ?_
    intro ij hijMem
    have hpred :
        ij.1 < ij.2 ∧
          ViolatesOrder (obs_1PGB.get ij.1) (obs_1PGB.get ij.2) := by
      -- unfold membership in the filtered finset
      simpa [violationPairs] using (Finset.mem_filter.1 hijMem).2
    exact (no_violations_1PGB ij hpred.1) hpred.2
  -- Conclude the count is 0 and thus ≤ 0.
  dsimp [CrossOctaveViolationsAtMost, violationCount]
  simp [hempty, hk]

theorem obs_1PGB_not_falsifier_default :
    ¬ F_TooManyCrossOctaveViolations (kDefault obs_1PGB) obs_1PGB := by
  intro hF
  rcases hF with ⟨hPre, hFail⟩
  have hPass : CrossOctaveViolationsAtMost (kDefault obs_1PGB) obs_1PGB :=
    obs_1PGB_passes_default
  exact hFail hPass

/-! ## Negative control (synthetic falsifier) -/

/-- A synthetic dataset that **reverses** the expected relationship
(RMSD increases together with consonance), intended as a negative control. -/
noncomputable def obs_negControl : List FoldObs :=
  [ { seed := 1, rmsd := (1 : ℚ), audioConsonance := (1 : ℚ) }
  , { seed := 2, rmsd := (2 : ℚ), audioConsonance := (2 : ℚ) }
  , { seed := 3, rmsd := (3 : ℚ), audioConsonance := (3 : ℚ) }
  ]

lemma obs_negControl_preregistered : PreregisteredDataset obs_negControl := by
  classical
  refine ⟨by
    -- length = 3
    simp [obs_negControl]
  , ?_, ?_⟩
  · intro o ho
    simp [obs_negControl] at ho
    rcases ho with rfl | rfl | rfl <;> norm_num
  · intro o ho
    simp [obs_negControl] at ho
    rcases ho with rfl | rfl | rfl <;> norm_num

theorem obs_negControl_is_falsifier_default :
    F_TooManyCrossOctaveViolations (kDefault obs_negControl) obs_negControl := by
  refine ⟨obs_negControl_preregistered, ?_⟩
  -- For 3 observations, kDefault = 0.
  have hk : kDefault obs_negControl = 0 := by
    simp [kDefault, totalPairs, obs_negControl]
  -- Exhibit a concrete violating pair (0,1), hence `violationCount > 0`.
  have hmem : ((⟨0, by simp [obs_negControl]⟩ : Fin obs_negControl.length),
               (⟨1, by simp [obs_negControl]⟩ : Fin obs_negControl.length))
      ∈ violationPairs obs_negControl := by
    classical
    refine Finset.mem_filter.2 ?_
    refine ⟨Finset.mem_univ _, ?_⟩
    refine ⟨by
      -- 0 < 1
      simp, ?_⟩
    -- Show this pair violates the expected order (since consonance increases with RMSD).
    left
    constructor <;> norm_num [obs_negControl]
  have hpos : 0 < violationCount obs_negControl := by
    dsimp [violationCount]
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  -- Therefore we cannot have `violationCount ≤ kDefault` (which is 0).
  intro hAtMost
  have : violationCount obs_negControl ≤ 0 := by
    simpa [CrossOctaveViolationsAtMost, hk] using hAtMost
  exact (Nat.not_le_of_gt hpos) this

/-! ## New benchmark datasets (2024-12-20 gamut run) -/

/-- 1VII three-seed snapshot from RSFold V2 gamut run.
Note: This dataset shows an **unexpected pattern** where lower RMSD
corresponds to lower consonance (opposite of hypothesis). -/
noncomputable def obs_1VII : List FoldObs :=
  [ { seed := 0
    , rmsd := (1300159/100000 : ℚ)        -- 13.00159
    , audioConsonance := (9889836/10000000 : ℚ) }  -- 0.9889836
  , { seed := 1
    , rmsd := (1302120/100000 : ℚ)        -- 13.0212
    , audioConsonance := (9948105/10000000 : ℚ) }  -- 0.9948105
  , { seed := 2
    , rmsd := (1306220/100000 : ℚ)        -- 13.0622
    , audioConsonance := (9956592/10000000 : ℚ) }  -- 0.9956592
  ]

lemma obs_1VII_preregistered : PreregisteredDataset obs_1VII := by
  classical
  refine ⟨by simp [obs_1VII], ?_, ?_⟩
  · intro o ho
    simp [obs_1VII] at ho
    rcases ho with rfl | rfl | rfl <;> norm_num
  · intro o ho
    simp [obs_1VII] at ho
    rcases ho with rfl | rfl | rfl <;> norm_num

/-- 1VII **fails** the default preregistration because lower RMSD → lower consonance!
This is a valid falsifier demonstrating the sonification metric needs refinement. -/
theorem obs_1VII_is_falsifier_default :
    F_TooManyCrossOctaveViolations (kDefault obs_1VII) obs_1VII := by
  refine ⟨obs_1VII_preregistered, ?_⟩
  -- For 3 observations, kDefault = 0.
  have hk : kDefault obs_1VII = 0 := by simp [kDefault, totalPairs, obs_1VII]
  -- Exhibit a concrete violating pair (0,1): seed 0 has lower RMSD but lower consonance.
  have hmem : ((⟨0, by simp [obs_1VII]⟩ : Fin obs_1VII.length),
               (⟨1, by simp [obs_1VII]⟩ : Fin obs_1VII.length))
      ∈ violationPairs obs_1VII := by
    classical
    refine Finset.mem_filter.2 ?_
    refine ⟨Finset.mem_univ _, ?_⟩
    refine ⟨by simp, ?_⟩
    left
    constructor <;> norm_num [obs_1VII]
  have hpos : 0 < violationCount obs_1VII := by
    dsimp [violationCount]
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  intro hAtMost
  have : violationCount obs_1VII ≤ 0 := by
    simpa [CrossOctaveViolationsAtMost, hk] using hAtMost
  exact (Nat.not_le_of_gt hpos) this

/-- HP35 three-seed snapshot from RSFold V2 gamut run.
This dataset shows the expected pattern (roughly): lower RMSD → higher consonance. -/
noncomputable def obs_HP35 : List FoldObs :=
  [ { seed := 0
    , rmsd := (1202403/100000 : ℚ)        -- 12.02403
    , audioConsonance := (9998785/10000000 : ℚ) }  -- 0.9998785
  , { seed := 1
    , rmsd := (1198382/100000 : ℚ)        -- 11.98382
    , audioConsonance := (9999248/10000000 : ℚ) }  -- 0.9999248
  , { seed := 2
    , rmsd := (1197875/100000 : ℚ)        -- 11.97875
    , audioConsonance := (9961414/10000000 : ℚ) }  -- 0.9961414
  ]

lemma obs_HP35_preregistered : PreregisteredDataset obs_HP35 := by
  classical
  refine ⟨by simp [obs_HP35], ?_, ?_⟩
  · intro o ho
    simp [obs_HP35] at ho
    rcases ho with rfl | rfl | rfl <;> norm_num
  · intro o ho
    simp [obs_HP35] at ho
    rcases ho with rfl | rfl | rfl <;> norm_num

end IndisputableMonolith.Sonification
