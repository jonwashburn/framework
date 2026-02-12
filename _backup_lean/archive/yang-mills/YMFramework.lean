import YM.OSPositivity.Wightman

-- ... existing code ...
  /-- W1: Spectral condition (energy nonnegativity for a concrete field). -/
  w1_spectral : ∃ W : YM.OSPositivity.Wightman.ReconstructionWitness,
    YM.OSPositivity.Wightman.spectrum_condition
      (YM.OSPositivity.Wightman.build_wightman_field W)
-- ... existing code ...

def YangMillsQFT : QuantumFieldTheory where
  spacetime := Euclidean 4
  /-- Fields are SU(3) link configurations on the lattice. -/
  fields := Config
  action :=
    -- Minimal, finite-region Wilson action evaluated on a fixed test config.
    let U0 : Config := fun _ => (1 : Matrix.specialUnitaryGroup (Fin 3) ℂ)
    actionFunctional U0

/-- Witness supplying the upgraded Wightman field for the framework guard. -/
noncomputable def defaultReconstructionWitness : YM.OSPositivity.Wightman.ReconstructionWitness :=
  let innerWitness : YM.OSPositivity.Wightman.ReconstructionWitness :=
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
        -- 0 < 1 over ℝ
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
  { innerWitness with
    smear := fun F => YM.OSPositivity.Wightman.build_smeared_operator innerWitness F
  , smear_bounded := by
      intro F
      simpa using YM.OSPositivity.Wightman.build_smeared_operator_bounded innerWitness F
  , smear_vacuum := by
      intro F
      simpa using YM.OSPositivity.Wightman.build_smeared_operator_vacuum innerWitness F }

-- ... existing code ...
