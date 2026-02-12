import YM.OSPositivity.OS2
import YM.OSPositivity.Wightman
import YM.OSPositivity.Euclid
import YM.OSWilson.Doeblin
import YM.OSWilson.Cluster
import YM.SpectralStability.RescaledNRC

/-!
CI Guards (spec-level): touch core acceptance symbols at top-level paths.
No axioms. No `sorry`. Props, not booleans.

TODO[Eight‑tick λ₁ extraction, Yang-Mills-sept21.tex 1313–1319]:
- The λ₁ enrichment used in spectrum-condition guards can be routed through the
  eight‑tick contraction extractor. Replace placeholders once the odd‑cone
  composition and Doeblin inputs are formalized.

TODO[Functional calculus, Yang-Mills-sept21.tex 1551–1560]:
- The spectrum-condition witnesses are currently tied to a spec-level slab
  inclusion. Upgrade to the functional-calculus identification `H ≈ −log T` and
  discharge the spectral inclusion via Riesz projections.
-/

namespace YM.CI.Guards

open YM.OSPositivity
open YM.OSWilson
open YM.SpectralStability

/-- Guard: OS2 positivity is present and usable. -/
def guard_os2 : Prop :=
  ∀ R, OS2.os2_positive (OS2.build_two_point R)

theorem guard_os2_holds : guard_os2 :=
  OS2.build_two_point_os2_positive

/-- Guard: Doeblin lower bound acceptance reachable. -/
def guard_doeblin_lower : Prop :=
  Doeblin.doeblin_lower_bound_spec Doeblin.build_doeblin_lower_bound

theorem guard_doeblin_lower_holds : guard_doeblin_lower :=
  Doeblin.build_doeblin_lower_bound_satisfies

/-- Guard: Cluster/character expansion and influence/Dobrushin specs are wired. -/
def guard_cluster : Prop :=
  let P : OSWilson.Cluster.SmallBeta := { β := 0.0, β_small := true }
  OSWilson.Cluster.influence_bound_spec P (OSWilson.Cluster.build_influence_bound P) ∧
  OSWilson.Cluster.cluster_expansion_spec P (OSWilson.Cluster.build_cluster_expansion P)

theorem guard_cluster_holds : guard_cluster := by
  let P : OSWilson.Cluster.SmallBeta := { β := 0.0, β_small := true }
  exact And.intro (OSWilson.Cluster.build_influence_bound_holds P)
                  (OSWilson.Cluster.build_cluster_expansion_holds P)

/-- Guard: Euclidean invariance limit assembled from rotation/translation specs. -/
def guard_euclid : Prop :=
  let rp : OSPositivity.Euclid.RotationApproxParams := { approx_error := 0.0, nonneg := (by decide) }
  let tp : OSPositivity.Euclid.TranslationLimitParams := { tightness := 0.0, nonneg := (by decide) }
  OSPositivity.Euclid.euclid_invariance_limit
    { rot_ok := OSPositivity.Euclid.rotation_approx_limit_spec rp
    , trans_ok := OSPositivity.Euclid.translation_limit_spec tp }

theorem guard_euclid_holds : guard_euclid := by
  let rp : OSPositivity.Euclid.RotationApproxParams := { approx_error := 0.0, nonneg := (by decide) }
  let tp : OSPositivity.Euclid.TranslationLimitParams := { tightness := 0.0, nonneg := (by decide) }
  have h := OSPositivity.Euclid.euclid_invariance_limit_holds rp tp rp.nonneg tp.nonneg
  simpa using h

/-/ Guard: NRC (all nonreal z) can be formed from a setup bundle. -/
def guard_nrc : Prop :=
  ∃ S : RescaledNRC.NRCSetup, RescaledNRC.NRC_all_nonreal S

theorem guard_nrc_holds : guard_nrc := by
  let proj : RescaledNRC.ProjectionControl := { Λ := 1.0, Λ_pos := by decide }
  let defect : RescaledNRC.GraphDefect := { a := 0.1, C := 2.0, bound_nonneg := by decide }
  let calib : RescaledNRC.Calibrator := { z0_im := 1.0, nonreal := by decide }
  let S : RescaledNRC.NRCSetup := { proj := proj, defect := defect, calib := calib
                                   , comparison := RescaledNRC.build_comparison_from_data proj defect calib }
  exact ⟨S, RescaledNRC.NRC_all_nonreal_holds S⟩

/-- Guard: Wightman spectrum condition acceptance available (canonical spec). -/
def guard_wightman : Prop :=
  ∃ W : OSPositivity.Wightman.ReconstructionWitness,
    OSPositivity.Wightman.spectrum_condition
      (OSPositivity.Wightman.build_wightman_field W)

theorem guard_wightman_holds : guard_wightman := by
  let innerWitness : OSPositivity.Wightman.ReconstructionWitness :=
    {
      N := 2
    , instN := by exact ⟨by decide⟩
    , β := 1
    , hβ := by
        -- 0 < 1 over ℝ
        simpa using (zero_lt_one : 0 < (1 : ℝ))
    , stateSpace := YM.OSPositivity.GNS.OSStateSpace (N := 2) (β := 1) (hβ := by
        simpa using (zero_lt_one : 0 < (1 : ℝ)))
    , stateSpace_isGNS := rfl
    , vacuum := 0
    , smear := fun F => YM.OSPositivity.LocalFields.smearOperator (N := 2) (β := 1) (hβ := by
        simpa using (zero_lt_one : 0 < (1 : ℝ))) F
    , smear_is_time_zero := ∀ F, YM.OSPositivity.LocalFields.smearOperator_domain (F := F)
    , smear_bounded := by
        intro F
        simpa using YM.OSPositivity.LocalFields.smearOperator_opNorm_le (N := 2) (β := 1) (hβ := by
          simpa using (zero_lt_one : 0 < (1 : ℝ))) F
    , smear_vacuum := by
        intro F
        simpa using YM.OSPositivity.LocalFields.smearOperator_vacuum (N := 2) (β := 1) (hβ := by
          simpa using (zero_lt_one : 0 < (1 : ℝ))) F
    , kernel := YM.OSPositivity.OS2.canonicalReflectionInput.kernel
    , nrc :=
        {
          proj := { Λ := 1, Λ_pos := by
            simpa using (zero_lt_one : 0 < (1 : ℝ)) }
        , defect := { a := 0, C := 0, bound_nonneg := by
            simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
        , calib := { z0_im := 1, nonreal := by
            simpa using (one_ne_zero : (1 : ℝ) ≠ 0) }
        , comparison := YM.SpectralStability.RescaledNRC.build_comparison_from_data
            { Λ := 1, Λ_pos := by
                simpa using (zero_lt_one : 0 < (1 : ℝ)) }
            { a := 0, C := 0, bound_nonneg := by
                simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
            { z0_im := 1, nonreal := by
                simpa using (one_ne_zero : (1 : ℝ) ≠ 0) } }
    , nrc_holds := YM.SpectralStability.RescaledNRC.NRC_all_nonreal_build _ _ _
    , gapWitness := { gamma_phys := 1, gamma_pos := by
        simpa using (zero_lt_one : 0 < (1 : ℝ)) } };
  let witness : OSPositivity.Wightman.ReconstructionWitness :=
    { innerWitness with
      smear := fun F => OSPositivity.Wightman.build_smeared_operator innerWitness F
    , smear_bounded := by
        intro F
        simpa using OSPositivity.Wightman.build_smeared_operator_bounded innerWitness F
    , smear_vacuum := by
        intro F
        simpa using OSPositivity.Wightman.build_smeared_operator_vacuum innerWitness F };
  refine ⟨witness, ?spec⟩
  ·
    -- Spectrum condition reduces to NRC witness and positive gap.
    simpa using OSPositivity.Wightman.build_wightman_field_satisfies witness

/-- Guard: Wightman spectrum condition with explicit λ₁ threading via default adapter. -/
def guard_wightman_with_lambda : Prop :=
  ∃ W : OSPositivity.Wightman.ReconstructionWitness,
    OSPositivity.Wightman.spectrum_condition
      (OSPositivity.Wightman.build_wightman_field
        (OSPositivity.Wightman.withDefaultLambdaOne W))

theorem guard_wightman_with_lambda_holds : guard_wightman_with_lambda := by
  -- Build a minimal reconstruction witness and apply the default λ₁ adapter
  let R := OSPositivity.OS2.canonicalReflectionInput
  let K := R.kernel
  let witness0 : OSPositivity.Wightman.ReconstructionWitness :=
    {
      N := 2
    , instN := by exact ⟨by decide⟩
    , β := 1
    , hβ := by simpa using (zero_lt_one : 0 < (1 : ℝ))
    , λ1 := 1
    , hλ1 := by simpa using (zero_lt_one : 0 < (1 : ℝ))
    , stateSpace := YM.OSPositivity.GNS.OSStateSpace (N := 2) (β := 1) (hβ := by
        simpa using (zero_lt_one : 0 < (1 : ℝ)))
    , stateSpace_isGNS := rfl
    , vacuum := 0
    , smear := fun _ ↦ id
    , smear_is_time_zero := ∀ F, YM.OSPositivity.LocalFields.smearOperator_domain (F := F)
    , kernel := K
    , nrc :=
        {
          proj := { Λ := 1, Λ_pos := by simpa using (zero_lt_one : 0 < (1 : ℝ)) }
        , defect := { a := 0, C := 0, bound_nonneg := by
            simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
        , calib := { z0_im := 1, nonreal := by
            simpa using (one_ne_zero : (1 : ℝ) ≠ 0) }
        , comparison := YM.SpectralStability.RescaledNRC.build_comparison_from_data
            { Λ := 1, Λ_pos := by simpa using (zero_lt_one : 0 < (1 : ℝ)) }
            { a := 0, C := 0, bound_nonneg := by
                simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
            { z0_im := 1, nonreal := by
                simpa using (one_ne_zero : (1 : ℝ) ≠ 0) } }
    , nrc_holds := YM.SpectralStability.RescaledNRC.NRC_all_nonreal_build _ _ _
    , gapWitness := { gamma_phys := 1, gamma_pos := by simpa using (zero_lt_one : 0 < (1 : ℝ)) } }
  refine ⟨witness0, ?_⟩
  simpa using OSPositivity.Wightman.build_wightman_field_satisfies
    (OSPositivity.Wightman.withDefaultLambdaOne witness0)

/-- Guard: Wightman spectrum condition with explicit eight‑tick λ₁ enrichment.
References: Yang-Mills-sept21.tex 1313–1319 (eight‑tick composition) for λ₁,
and 1551–1560 (functional calculus) for the Hamiltonian narrative. -/
def guard_wightman_with_eight_tick : Prop :=
  ∃ W : OSPositivity.Wightman.ReconstructionWitness,
    OSPositivity.Wightman.spectrum_condition
      (OSPositivity.Wightman.build_wightman_field
        (OSPositivity.Wightman.withEightTickLambdaOne W))

theorem guard_wightman_with_eight_tick_holds : guard_wightman_with_eight_tick := by
  -- Build a minimal reconstruction witness and apply the eight‑tick λ₁ adapter
  let R := OSPositivity.OS2.canonicalReflectionInput
  let K := R.kernel
  let witness0 : OSPositivity.Wightman.ReconstructionWitness :=
    {
      N := 2
    , instN := by exact ⟨by decide⟩
    , β := 1
    , hβ := by simpa using (zero_lt_one : 0 < (1 : ℝ))
    , λ1 := 1
    , hλ1 := by simpa using (zero_lt_one : 0 < (1 : ℝ))
    , stateSpace := YM.OSPositivity.GNS.OSStateSpace (N := 2) (β := 1) (hβ := by
        simpa using (zero_lt_one : 0 < (1 : ℝ)))
    , stateSpace_isGNS := rfl
    , vacuum := 0
    , smear := fun _ ↦ id
    , smear_is_time_zero := ∀ F, YM.OSPositivity.LocalFields.smearOperator_domain (F := F)
    , kernel := K
    , nrc :=
        {
          proj := { Λ := 1, Λ_pos := by simpa using (zero_lt_one : 0 < (1 : ℝ)) }
        , defect := { a := 0, C := 0, bound_nonneg := by
            simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
        , calib := { z0_im := 1, nonreal := by
            simpa using (one_ne_zero : (1 : ℝ) ≠ 0) }
        , comparison := YM.SpectralStability.RescaledNRC.build_comparison_from_data
            { Λ := 1, Λ_pos := by simpa using (zero_lt_one : 0 < (1 : ℝ)) }
            { a := 0, C := 0, bound_nonneg := by
                simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
            { z0_im := 1, nonreal := by
                simpa using (one_ne_zero : (1 : ℝ) ≠ 0) } }
    , nrc_holds := YM.SpectralStability.RescaledNRC.NRC_all_nonreal_build _ _ _
    , gapWitness := { gamma_phys := 1, gamma_pos := by simpa using (zero_lt_one : 0 < (1 : ℝ)) } }
  refine ⟨witness0, ?_⟩
  simpa using OSPositivity.Wightman.build_wightman_field_satisfies
    (OSPositivity.Wightman.withEightTickLambdaOne witness0)

end YM.CI.Guards
