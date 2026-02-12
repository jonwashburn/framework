import YM.OSPositivity.OS2
import YM.Continuum.Limit
import YM.OSPositivity.Wightman

/-!
Clay Final Theorem (spec-level): OS/Wightman acceptance with a positive continuum gap γ₀.
No axioms. No `sorry`.

References: Yang-Mills-sept21.tex — spectral gap persistence and OS→Wightman
construction (see Theorem 2097 and surrounding Riesz projection discussion).
Roadmap: `YM/Docs/OSPlan.md` catalogues outstanding lemmas and module TODOs.

TODO[Mass-gap certification]:
- Replace the placeholders in this file with the actual mass-gap theorem once
  OS0–OS5 and OS→Wightman reconstruction are formalized (cf. Theorem~\ref{thm:global-OS0-5},
  Thm.~\ref{thm:gap-persist-cont}).
- Document the dependencies: transfer contraction (Thm.~\ref{thm:eight-tick-uniform}),
  heat-kernel NRC convergence (Cor.~\ref{cor:nrc-allz-fixed}), reflection positivity,
  clustering, and analytic continuation.
- Align with the roadmap in `YM/Docs/OSPlan.md`, keeping TODO markers synchronized.
- Record the need for OS2 inputs from `YM/OSPositivity/OS2.lean`, local fields from
  `YM/OSPositivity/LocalFields.lean`, clustering from `YM/OSPositivity/Clustering.lean`,
  and reconstruction outputs from `YM/OSPositivity/Wightman.lean`.
-/

namespace YM.Clay.Final

open YM.OSPositivity

/-- Minimal inputs for the final acceptance: a strictly positive gap `γ₀`. -/
-- TODO[Parameter enrichment]: include the continuum limit data (van Hove sequence,
-- smearing radii) once the full mass-gap pipeline is formalized, referencing the
-- Euclidean modulus in `YM/OSPositivity/Euclid.lean` and the Schwinger inputs.
structure FinalParams where
  gamma0 : ℝ
  hpos   : 0 < gamma0

/-- Final acceptance payload: records `γ₀` together with OS2 and Wightman witnesses. -/
-- TODO[Acceptance payload]: expand to carry the reconstructed Hilbert space,
-- Hamiltonian, gap witness, and clustering certificate when available, importing
-- the exponential decay controls from `YM/OSPositivity/Clustering.lean`.
structure FinalAcceptance where
  gamma0 : ℝ
  os2    : OS2.TwoPoint
  witness : Wightman.ReconstructionWitness
  wight  : Wightman.WightmanField
  Hop    : witness.stateSpace →L[ℂ] witness.stateSpace
  gap    : ℝ

/-- Spec: `γ₀` is positive and the OS2/Wightman acceptance predicates hold. -/
-- TODO[Mass-gap spec]: relate this specification to the Minkowski Hamiltonian
-- gap extracted from OS reconstruction (Yang-Mills-sept21.tex lines 1551–1560)
-- once `YM/OSPositivity/Wightman.lean` carries the reconstructed Hamiltonian and
-- the gap witness from `YM/SpectralStability/Persistence.lean`.
def final_spec (P : FinalParams) (A : FinalAcceptance) : Prop :=
  (A.gamma0 = P.gamma0) ∧
  (OS2.os2_positive A.os2) ∧
  (Wightman.spectrum_condition A.wight) ∧
  (P.hpos)

/-- Builder: instantiates OS2/Wightman witnesses and carries through `γ₀`.
TODO[Dependency threading]: update this builder to reference the Lean proofs of
OS2 reflection positivity, OS→Wightman reconstruction, and spectral-gap
persistence once available, as detailed in `YM/Docs/OSPlan.md`.
TODO[Mass-gap builder]: instantiate this via the actual OS→W reconstruction
once all dependencies are formalized, using the smeared local fields from
`YM/OSPositivity/LocalFields.lean` and the clustering bounds from
`YM/OSPositivity/Clustering.lean`. -/
def build_final (P : FinalParams) : FinalAcceptance :=
  let witness0 : Wightman.ReconstructionWitness :=
    {
      N := 2
    , instN := by exact ⟨by decide⟩
    , β := 1
    , hβ := by
        -- 0 < 1 over ℝ
        simpa using (zero_lt_one : 0 < (1 : ℝ))
    , λ1 := 0
    , hλ1 := by
        -- placeholder; immediately overwritten below via withLambdaOne
        have : 0 < (1 : ℝ) := by simpa using (zero_lt_one : 0 < (1 : ℝ))
        exact this
    , stateSpace := YM.OSPositivity.GNS.OSStateSpace (N := 2) (β := 1) (hβ := by
        simpa using (zero_lt_one : 0 < (1 : ℝ)))
    , stateSpace_isGNS := rfl
    , vacuum := 0
    , smear := fun _ ↦ id -- TODO[Time-zero insertion]: replace identity with genuine smeared operators.
    , smear_is_time_zero := ∀ F, YM.OSPositivity.LocalFields.smearOperator_domain (F := F) -- TODO[OS4 symmetry → time-zero algebra]: supply proof once permutation symmetry is formalized.
    , kernel := YM.OSPositivity.OS2.canonicalReflectionInput.kernel
    , nrc :=
        {
          proj := { Λ := 1, Λ_pos := by
            -- 0 < 1 over ℝ
            simpa using (zero_lt_one : 0 < (1 : ℝ)) }
        , defect := { a := 0, C := 0, bound_nonneg := by
            -- 0 ≤ 0 over ℝ
            simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
        , calib := { z0_im := 1, nonreal := by
            -- 1 ≠ 0 over ℝ
            simpa using (one_ne_zero : (1 : ℝ) ≠ 0) }
        , comparison := YM.SpectralStability.RescaledNRC.build_comparison_from_data
            { Λ := 1, Λ_pos := by
                simpa using (zero_lt_one : 0 < (1 : ℝ)) }
            { a := 0, C := 0, bound_nonneg := by
                simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
            { z0_im := 1, nonreal := by
                simpa using (one_ne_zero : (1 : ℝ) ≠ 0) } }
    , nrc_holds := YM.SpectralStability.RescaledNRC.NRC_all_nonreal_build _ _ _
    , gapWitness := {
        gamma_phys := P.gamma0
      , gamma_pos := P.hpos } };
  -- Build contraction parameters from the continuum witness and thread λ₁
  let Pλ : OSPositivity.Euclid.FromContraction.Params :=
    { N := witness0.N
    , instN := witness0.instN
    , β := witness0.β
    , β_pos := witness0.hβ
    , λ1 := OSPositivity.OS2.continuumLambda₁ OSPositivity.OS2.canonicalReflectionInput.witness
    , λ1_pos := OSPositivity.OS2.continuumLambda₁_pos OSPositivity.OS2.canonicalReflectionInput.witness
    , lattice_dim := 4
    , dim_pos := by decide }
  -- Thread λ₁ into the reconstruction witness directly from contraction Params
  let witness := Wightman.withLambdaOneFromParams witness0 Pλ
  let w := Wightman.build_wightman_field witness
  { gamma0 := P.gamma0
  , os2    := OS2.build_two_point {
      witness := YM.Continuum.Limit.defaultWitness 1 (by
        -- 0 < 1 over ℝ
        simpa using (zero_lt_one : 0 < (1 : ℝ)))
      , observable_value := 0 }
  , witness := witness
  , wight  := w
  , Hop    := w.ham.Hop
  , gap    := w.ham.gap }

/-- The Hamiltonian surrogate in the final acceptance has a certified gap,
exported from the spectral slab inclusion predicate. -/
lemma final_gap_certified (A : FinalAcceptance) :
  YM.SpectralStability.Persistence.spec_slab_inclusion A.Hop A.gap := by
  -- Obtained from the `Wightman` witness
  have := A.wight.ham.spectral_gap_spec
  simpa [YM.SpectralStability.Persistence.spec_slab_inclusion] using this

/-- Operator-aware slab inclusion exported from the reconstructed Hamiltonian. -/
lemma final_slab_inclusion_op (A : FinalAcceptance) :
  YM.SpectralStability.Persistence.spec_slab_inclusion_op A.Hop A.gap := by
  -- Immediate from the Hamiltonian field
  simpa using A.wight.ham.spectral_gap_spec

/-- Spec-level acceptance theorem for the Clay certificate. -/
-- TODO[Final theorem upgrade]: replace this spec-level statement with the actual
-- mass-gap theorem once OS0–OS5, reconstruction, and gap persistence are formalized.
theorem build_final_holds (P : FinalParams) :
  final_spec P (build_final P) := by
  dsimp [final_spec, build_final]
  refine And.intro rfl ?rest
  refine And.intro ?hOS2 (And.intro ?hW ?hγ)
  · -- TODO[OS2 input]: once `OS2.build_two_point` encodes the true reflection-positive
    -- Schwinger data, this step should cite the completed proof in `YM/OSPositivity/OS2.lean`.
    exact OS2.build_two_point_os2_positive _ (by simp)
  · -- Spectrum condition follows from the Hamiltonian gap witness.
    have := Wightman.build_wightman_field_satisfies _
    simpa using this
  · exact P.hpos

end YM.Clay.Final
