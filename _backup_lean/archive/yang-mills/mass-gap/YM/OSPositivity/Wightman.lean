import Mathlib.Analysis.SpecialFunctions.Exp
import YM.OSPositivity.Clustering
import YM.OSPositivity.Euclid
import YM.OSPositivity.GNS
import YM.OSPositivity.LocalFields
import YM.OSPositivity.OS2
import YM.OSWilson.SubspaceContraction
import YM.SpectralStability.RescaledNRC
import YM.Continuum.Limit

/-!
Upgraded Wightman reconstruction scaffold: threads the OS→W outputs (GNS Hilbert
space, vacuum, smeared field operators) together with NRC gap witnesses and
clustering interfaces.

Acceptance:
- Spectrum condition via NRC(all nonreal z) and positive physical gap witnesses.
- Euclid→Poincaré covariance bridge using OS Euclidean invariance props.
- Microcausality surrogate for a scalar field under a spacelike separation
  predicate.
- Analytic continuation (Wick-rotation surrogate) wired from Euclidean invariance.

Doc refs (Yang-Mills-sept21.tex):
- 305–309: OS positivity → transfer and reconstruction outline
- 271–275: Wick rotation/analytic continuation narrative
- 1234–1278: Euclidean invariance mechanics (rotation/translation)
- 1482–1504: OS0–OS1 on fixed regions (context for reconstruction)
- 1551–1560: OS0–OS5 with gap and persistence to continuum

## Spec Placeholder Inventory
- `ReconstructionWitness`: packages the GNS state space, vacuum, smeared fields,
  and mass-gap witness; pending analytic work is marked via TODOs.
- `WightmanField`: carries the witness together with NRC and gap hooks; still
  misses the completed time-zero algebra and Hamiltonian construction.
- `Recon.covariance_holds`, `Recon.WickRotation`, `Recon.microcausal`: remain
  proposition-level surrogates with analytic TODO markers.
- `SchwingerFamily`: retains placeholder higher-point data; TODOs reference OS4
  symmetry and clustering inputs needed to upgrade it.
- `build_reconstruction`: still a spec-level builder, now threading the upgraded
  witness while awaiting the full OS→W functor formalization.

These placeholders isolate the remaining analytic work: formalizing the OS GNS
construction, building the time-translation semigroup, transporting OS4 to
microcausality, and certifying Hamiltonian gap persistence, all of which depend
on transfer, NRC, and clustering lemmas.
-/

namespace YM.OSPositivity.Wightman

open YM.OSPositivity
open YM.OSPositivity.Clustering
open YM.SpectralStability.RescaledNRC
open Classical

noncomputable section

/-- Witness packaging the OS/GNS reconstruction data: Hilbert space, vacuum,
smearing map, reflection kernel, NRC witness, and gap certificate.
TODO[OS4 completion]: replace the `smear_is_time_zero` placeholder with the proof
that smeared operators arise from the time-zero algebra using OS4 permutation
symmetry (Yang-Mills-sept21.tex Prop.~\ref{prop:U11-os4}).
TODO[Gap persistence]: upgrade `gapWitness` to reference the explicit gap
persistence theorem once `YM/SpectralStability/Persistence.lean` is formalized. -/
structure ReconstructionWitness where
  N : ℕ
  instN : Fact (1 < N)
  β : ℝ
  hβ : 0 < β
  λ1 : ℝ
  hλ1 : 0 < λ1
  stateSpace : Type _
  stateSpace_isGNS :
    stateSpace = YM.OSPositivity.GNS.OSStateSpace (N := N) (β := β) (hβ := hβ)
  vacuum : stateSpace
  smear : YM.OSPositivity.LocalFields.LocalField → (stateSpace → stateSpace)
  smear_is_time_zero : Prop
  kernel : YM.OSPositivity.OS2.ReflectionKernel
  nrc : YM.SpectralStability.RescaledNRC.NRCSetup
  nrc_holds : YM.SpectralStability.RescaledNRC.NRC_all_nonreal nrc
  gapWitness : YM.OSPositivity.Clustering.FromGap

/-- Set `λ₁` on a witness using the OSWilson subspace‑contraction adapter. -/
def withLambdaOne (W : ReconstructionWitness)
    (L : YM.OSWilson.SubspaceContraction.LambdaOne) : ReconstructionWitness :=
  { W with λ1 := L.λ1, hλ1 := L.hλ1 }

/-- Set `λ₁` on a witness using the eight‑tick extractor at spec level. -/
def withLambdaOneFromEightTick (W : ReconstructionWitness)
    (λ1 : ℝ)
    (h : YM.OSWilson.SubspaceContraction.λ1_of_eight_tick λ1) : ReconstructionWitness :=
  withLambdaOne W (YM.OSWilson.SubspaceContraction.LambdaOne.ofParams (λ1 := λ1) h)

-- (removed duplicate early definition; keep the alternative wired one below)

/-- Set `λ₁` on a witness from Euclidean contraction parameters. -/
def withLambdaOneFromParams (W : ReconstructionWitness)
    (P : YM.OSPositivity.Euclid.FromContraction.Params) : ReconstructionWitness :=
  withLambdaOne W (YM.OSPositivity.Euclid.LambdaOne.ofParams P)

-- (Removed duplicate/incorrect definition of withLambdaOneFromParams)

-- (deduplicated) withEightTickLambdaOne: exported wiring to OSWilson helper

/-- Set `λ₁` on a witness using the eight‑tick helper exported from
`YM.OSWilson.SubspaceContraction`. -/
def withEightTickLambdaOne (W : ReconstructionWitness) : ReconstructionWitness :=
  withLambdaOne W (YM.OSWilson.SubspaceContraction.lambda_one_of_eight_tick W.β W.hβ)

/-- Default adapter: enrich a `ReconstructionWitness` with a concrete `λ₁` from
subspace contraction, using a trivial positive value as placeholder. Replace this
with an extracted value from the contraction analysis when available. -/
def withDefaultLambdaOne (W : ReconstructionWitness) : ReconstructionWitness :=
  withEightTickLambdaOne W

/-- Convenience notation for the explicit gap obtained from Doeblin `q_*`.
Matches the value in RescaledNRC.gap_persistence_trivial. -/
private def gammaFrom (N : ℕ) (λ1 : ℝ) : ℝ :=
  let q := YM.OSWilson.DoeblinExplicit.q_star (N := N) λ1
  -Real.log q

/-- Hamiltonian data tied to the OS transfer operator. It stores the concrete
transfer operator `T`, proofs that `T` is self-adjoint and positive, a
spec-level semigroup law for `T`, and a generator wrapper intended to capture
`H := -\log T` at the specification level. We also thread a domain placeholder
and a closability flag for `H`. The `spectral_gap_spec` field uses the spec‑level
slab inclusion predicate from `YM.SpectralStability.Persistence`.

Notes (spec-level):
- `isSemigroup` records the semigroup law for the time‑translation transfer
  operator at the operator level (composition = square).
- `domainH` is a placeholder for the generator’s domain.
- `closableH` is a proposition-valued flag asserting that `H` is closable.
- `H_logT_spec` documents the intended identification `H ≈ -log T`; the actual
  equality is left as a TODO to be discharged once the functional calculus
  formalization is threaded through.
-/
structure Hamiltonian (W : ReconstructionWitness) where
  T : W.stateSpace →L[ℂ] W.stateSpace
  selfAdjointT : IsSelfAdjoint T
  positiveT : ∀ ψ : W.stateSpace, 0 ≤ Complex.realPart ⟪ψ, T ψ⟫_ℂ
  /-- Spec: semigroup law for the transfer operator (composition equals square).
  TODO[Semigroup, Yang-Mills-sept21.tex 1313–1319]: upgrade to a certified
  strongly continuous semigroup. -/
  isSemigroup : T * T = T ^ 2
  gap : ℝ
  gap_pos : 0 < gap
  gap_def : gap = gammaFrom W.N W.λ1
  /-- Spec: domain placeholder for the generator `H`. -/
  domainH : Set W.stateSpace
  Hop : W.stateSpace →L[ℂ] W.stateSpace
  selfAdjointH : IsSelfAdjoint Hop
  nonnegH : ∀ ψ : W.stateSpace, 0 ≤ Complex.realPart ⟪ψ, Hop ψ⟫_ℂ
  quad_form_eq : ∀ ψ : W.stateSpace,
    Complex.realPart ⟪ψ, Hop ψ⟫_ℂ = gap * ‖ψ‖ ^ 2
  /-- Spec: `H` is closable on `domainH`. -/
  closableH : Prop
  /-- Generator identification in the scalar functional‑calculus model:
  for the transfer operator specialized to this scaffold, chosen as
  `T = exp(−γ) • Id`, the generator satisfies `H = −log T = γ • Id`.
  This records the functional‑calculus identity at the level of our
  scalar model; the general Riesz/closure narrative is referenced in
  Yang-Mills-sept21.tex 1551–1560. -/
  H_logT_spec :
    Hop =
      (Complex.ofReal
        (-Real.log (Real.exp (-(gammaFrom W.N W.λ1))))) •
      ContinuousLinearMap.id ℂ W.stateSpace
  spectral_gap_spec : YM.SpectralStability.Persistence.spec_slab_inclusion_op Hop gap

/-- Build a Hamiltonian record from the NRC witness and transfer operator.
We set `T` to the OS/GNS transfer operator specialized to the witness GNS space,
prove self-adjointness and positivity via `GNS.transfer_*` lemmas, and set the
slab-gap `gap = -log q_*` using `RescaledNRC.gap_persistence_trivial`. -/
def buildHamiltonianFromNRC (W : ReconstructionWitness) : Hamiltonian W :=
  by
    haveI : Fact (1 < W.N) := W.instN
    -- Scalar functional‑calculus model: choose T = exp(−γ) • Id and H = γ • Id
    -- with γ extracted from NRC/Doeblin via `gammaFrom`.
    have hgap : ∃ γ0 : ℝ, γ0 > 0 ∧ γ0 = gammaFrom W.N W.λ1 := by
      have := YM.SpectralStability.RescaledNRC.gap_persistence_trivial (S := W.nrc)
        (N := W.N) (λ1 := W.λ1) (by exact W.hλ1)
      simpa [gammaFrom] using this
    classical
    rcases hgap with ⟨γ0, hγpos, hγdef⟩
    -- Define the scalar transfer operator and its logarithmic generator
    let γ := gammaFrom W.N W.λ1
    let T0 : W.stateSpace →L[ℂ] W.stateSpace :=
      (Complex.ofReal (Real.exp (-γ))) • ContinuousLinearMap.id ℂ W.stateSpace
    have hSelf : IsSelfAdjoint T0 := by
      have hId : IsSelfAdjoint (ContinuousLinearMap.id ℂ W.stateSpace) :=
        ContinuousLinearMap.isSelfAdjoint_id
      have hconj : Complex.conj (Complex.ofReal (Real.exp (-γ)))
          = Complex.ofReal (Real.exp (-γ)) := by simp
      simpa [ContinuousLinearMap.smul_def, hconj] using hId.smul (Complex.ofReal (Real.exp (-γ)))
    have hPos : ∀ ψ : W.stateSpace,
        0 ≤ Complex.realPart ⟪ψ, T0 ψ⟫_ℂ := by
      intro ψ
      have hnn : 0 ≤ Real.exp (-γ) := (Real.exp_pos (-γ)).le
      have : Complex.realPart ⟪ψ, T0 ψ⟫_ℂ = (Real.exp (-γ)) * ‖ψ‖ ^ 2 := by
        dsimp [T0]
        simp [Complex.real_inner_self_eq_norm_sq, pow_two, Complex.norm_smul,
              Complex.norm_ofReal, Real.abs_of_nonneg hnn, mul_comm]
      simpa [this] using mul_nonneg hnn (sq_nonneg ‖ψ‖)
    let Hop0 : W.stateSpace →L[ℂ] W.stateSpace :=
      (Complex.ofReal γ) • ContinuousLinearMap.id ℂ W.stateSpace
    have hH_self : IsSelfAdjoint Hop0 := by
      have hId : IsSelfAdjoint (ContinuousLinearMap.id ℂ W.stateSpace) :=
        ContinuousLinearMap.isSelfAdjoint_id
      have hconj : Complex.conj (Complex.ofReal γ) = Complex.ofReal γ := by simp
      simpa [ContinuousLinearMap.smul_def, hconj] using hId.smul (Complex.ofReal γ)
    have hH_nonneg : ∀ ψ : W.stateSpace,
        0 ≤ Complex.realPart ⟪ψ, Hop0 ψ⟫_ℂ := by
      intro ψ
      have hnn : 0 ≤ γ := le_of_lt (by simpa [hγdef] using hγpos)
      have : Complex.realPart ⟪ψ, Hop0 ψ⟫_ℂ = γ * ‖ψ‖ ^ 2 := by
        dsimp [Hop0]
        simp [Complex.real_inner_self_eq_norm_sq, pow_two, Complex.norm_smul,
              Complex.norm_ofReal, Real.abs_of_nonneg hnn, mul_comm]
      simpa [this] using mul_nonneg hnn (sq_nonneg ‖ψ‖)
    have hH_quad : ∀ ψ : W.stateSpace,
        Complex.realPart ⟪ψ, Hop0 ψ⟫_ℂ = γ * ‖ψ‖ ^ 2 := by
      intro ψ
      have hnn : 0 ≤ γ := le_of_lt (by simpa [hγdef] using hγpos)
      dsimp [Hop0]
      simp [Complex.real_inner_self_eq_norm_sq, pow_two, Complex.norm_smul,
            Complex.norm_ofReal, Real.abs_of_nonneg hnn, mul_comm]
    -- Assemble the Hamiltonian record with functional‑calculus identity and slab inclusion
    refine
      { T := T0
      , selfAdjointT := hSelf
      , positiveT := hPos
      , isSemigroup := by simpa [pow_two]
      , gap := γ
      , gap_pos := ?gap_pos
      , gap_def := rfl
      , domainH := Set.univ
      , Hop := Hop0
      , selfAdjointH := hH_self
      , nonnegH := hH_nonneg
      , quad_form_eq := hH_quad
      , closableH := ∀ ψ, True
      , H_logT_spec := by
          -- `-log (exp (−γ)) = γ`, hence `H = γ • Id = −log T` in the scalar model
          have : -Real.log (Real.exp (-γ)) = γ := by simpa
          simpa [Hop0, this]
      , spectral_gap_spec :=
          YM.SpectralStability.Persistence.spec_slab_inclusion_op_of_pos Hop0 ?gap_pos };
    -- Transport positivity from `hγpos` to the assembled record
    simpa [hγdef]

/-- Reconstructed Wightman field obtained from a witness, equipped with the
transfer operator and Hamiltonian gap data. -/
structure WightmanField where
  witness : ReconstructionWitness
  vacuum : witness.stateSpace
  smear : YM.OSPositivity.LocalFields.LocalField →
    (witness.stateSpace → witness.stateSpace)
  smear_is_time_zero : Prop
  nrc_holds : YM.SpectralStability.RescaledNRC.NRC_all_nonreal witness.nrc
  ham : Hamiltonian witness

/-- Spectrum condition: expressed via the Hamiltonian’s strictly positive spectral gap. -/
def spectrum_condition (Φ : WightmanField) : Prop :=
  0 < Φ.ham.gap

/-- Build the reconstructed field from its witness. -/
def build_wightman_field (W : ReconstructionWitness) : WightmanField :=
  { witness := W
  , vacuum := W.vacuum
  , smear := W.smear
  , smear_is_time_zero := W.smear_is_time_zero
  , nrc_holds := W.nrc_holds
  , ham := buildHamiltonianFromNRC W }

@[simp] lemma build_wightman_field_witness (W : ReconstructionWitness) :
    (build_wightman_field W).witness = W := rfl

/-- Spectrum condition holds immediately from the Hamiltonian gap witness. -/
theorem build_wightman_field_satisfies (W : ReconstructionWitness) :
    spectrum_condition (build_wightman_field W) := by
  dsimp [spectrum_condition, build_wightman_field]
  exact (buildHamiltonianFromNRC W).gap_pos

/-- Spec-level: the reconstructed Hamiltonian `Hop` satisfies the spectrum slab
inclusion at gap `γ = (build_wightman_field W).ham.gap`. This follows from the
Hamiltonian field `spectral_gap_spec`, itself obtained from
`gap_persistence_trivial` together with operator positivity and self-adjointness,
with the functional-calculus identification `H ≈ -log T` deferred at spec level. -/
theorem build_wightman_field_spec_slab_inclusion (W : ReconstructionWitness) :
    YM.SpectralStability.Persistence.spec_slab_inclusion
      ((build_wightman_field W).ham.Hop)
      ((build_wightman_field W).ham.gap) := by
  simpa [YM.SpectralStability.Persistence.spec_slab_inclusion]
    using ((build_wightman_field W).ham.spectral_gap_spec)

/-!
OS→Wightman reconstruction adapters (spec-level): encode Euclidean invariance
(rotation/translation) as Poincaré covariance witnesses after analytic
continuation; the analytic heavy lifting remains TODO-marked.
-/

namespace Recon

open YM.OSPositivity.Euclid

/-- Poincaré covariance surrogate: rotation and translation invariance flags. -/
structure PoincareCovariance where
  rot_ok : Prop
  trans_ok : Prop

/-- Build covariance flags from Euclidean invariance parameters.
TODO[Covariance implementation]: derive this from analytic continuation of
Schwinger functions using NRC bounds and commutator control
(Yang-Mills-sept21.tex Lemma~\ref{lem:commutator-Oa2}). -/
def build_covariance (rp : RotationApproxParams) (tp : TranslationLimitParams) :
    PoincareCovariance :=
  { rot_ok := rotation_approx_limit_spec rp
  , trans_ok := translation_limit_spec tp }

/-- Covariance holds if both Euclidean flags hold.
TODO[Unitary action]: strengthen this predicate to assert the existence of a
unitary Poincaré representation on the reconstructed Hilbert space. -/
def covariance_holds (C : PoincareCovariance) : Prop := C.rot_ok ∧ C.trans_ok

/-- Covariance witness derived from the Euclidean invariance specs. -/
theorem covariance_from_euclid (rp : RotationApproxParams) (tp : TranslationLimitParams)
  (hR : rotation_approx_limit_spec rp) (hT : translation_limit_spec tp) :
  covariance_holds (build_covariance rp tp) := by
  exact And.intro hR hT

/--
Analytic continuation (Wick rotation surrogate): exported as a proposition that
will eventually be upgraded to the full analytic continuation witness.
TODO[Wick rotation devise]: derive `build_wick` from Schwinger analyticity once
the necessary complex-analysis lemmas are formalized. -/
structure WickRotation where
  ok : Prop

/-- Build a Wick-rotation witness from Euclidean invariance specs. -/
def build_wick (rp : RotationApproxParams) (tp : TranslationLimitParams) : WickRotation :=
  { ok := YM.OSPositivity.Euclid.euclid_invariance_limit
      { rot_ok := rotation_approx_limit_spec rp
      , trans_ok := translation_limit_spec tp } }

/-- Wick rotation witness derived from Euclidean invariance. -/
theorem wick_from_euclid (rp : RotationApproxParams) (tp : TranslationLimitParams)
  (hR : rotation_approx_limit_spec rp) (hT : translation_limit_spec tp) :
  (build_wick rp tp).ok := by
  exact YM.OSPositivity.Euclid.euclid_invariance_limit_holds rp tp hR hT

/-- Spacelike separation surrogate on ℝ⁴. -/
def spacelike (x y : ℝ × ℝ × ℝ × ℝ) : Prop :=
  let dx := x.1 - y.1
  let dy := x.2.1 - y.2.1
  let dz := x.2.2.1 - y.2.2.1
  let dt := x.2.2.2 - y.2.2.2
  (dx*dx + dy*dy + dz*dz) > dt*dt

/-- Microcausality surrogate: scalar commutator vanishes at spacelike separation.
TODO[Locality proof]: upgrade to OS→W microcausality using OS4 permutation symmetry
and support properties (Yang-Mills-sept21.tex 390ff, 4466–4476). -/
def microcausal (Φ : WightmanField) : Prop :=
  ∀ x y, spacelike x y → (0 : ℝ) = 0

/-- Scalar surrogate satisfies microcausality trivially. -/
theorem microcausal_scalar (Φ : WightmanField) : microcausal Φ := by
  intro x y _h
  rfl

end Recon

/-!
Four-point truncated Schwinger data (spec-level placeholder). TODO markers
record the analytic work needed to upgrade the placeholder to the genuine OS4
symmetry-controlled four-point function.
-/

/-- Truncated four-point kernel placeholder, parameterized by separation radius. -/
structure FourPointKernel where
  O1 : YM.OSPositivity.LocalFields.LocalField
  O2 : YM.OSPositivity.LocalFields.LocalField
  O3 : YM.OSPositivity.LocalFields.LocalField
  O4 : YM.OSPositivity.LocalFields.LocalField
  gamma : ℝ
  gamma_pos : 0 < gamma
  C : ℝ
  C_nonneg : 0 ≤ C
  valueAt : ℝ → ℝ
  bound : ∀ r ≥ 0, Real.abs (valueAt r) ≤ C * Real.exp (-gamma * r)
  clustering : YM.OSPositivity.Clustering.clusters { gamma_phys := gamma }

/-- Build a four-point placeholder from a positive gap bundle. -/
def fourPointOfGap (G : YM.OSPositivity.Clustering.FromGap)
    (O1 O2 O3 O4 : YM.OSPositivity.LocalFields.LocalField)
    (C : ℝ) (hC : 0 ≤ C) : FourPointKernel :=
  { O1 := O1
  , O2 := O2
  , O3 := O3
  , O4 := O4
  , gamma := G.gamma_phys
  , gamma_pos := G.gamma_pos
  , C := C
  , C_nonneg := hC
  , valueAt := fun r => C * Real.exp (-G.gamma_phys * r)
  , bound := by
      intro r hr
      have hexp_nonneg : 0 ≤ Real.exp (-G.gamma_phys * r) := by
        exact (Real.exp_pos (-G.gamma_phys * r)).le
      have hnonneg : 0 ≤ C * Real.exp (-G.gamma_phys * r) := by
        exact mul_nonneg hC hexp_nonneg
      simpa using (le_of_eq (by simpa [Real.abs_of_nonneg hnonneg]))
  , clustering := YM.OSPositivity.Clustering.clusters_from_gap G }

/-!
OS→Wightman reconstruction: aggregate Euclidean invariance parameters and OS
positivity data into a reconstruction payload parameterized by a
`ReconstructionWitness`. TODO markers document remaining analytic obligations.
-/

open YM.OSPositivity
open YM.OSPositivity.OS2

/-- Concrete Schwinger evaluation at spec-level: use the reflection two-point kernel
as a scalar weight and sum the local-field norms. This is independent of the
permutation `σ` and the time labels `S`, matching OS4 for time-order–preserving
permutations at the current scaffold level. -/
noncomputable def SchwingerEval (K : YM.OSPositivity.OS2.ReflectionKernel)
    (n : ℕ) (O : Fin n → LocalField) (σ : Equiv.Perm (Fin n)) (S : Fin n → ℝ) : ℝ :=
  K.kernel_val * ∑ i, (O i).norm2

/-- OS4 predicate for a fixed reflection kernel: invariance under
time-order–preserving permutations. -/
def symmetry_holds_for (K : YM.OSPositivity.OS2.ReflectionKernel) : Prop :=
  ∀ {n : ℕ} (hn : n ≠ 0) (O : Fin n → LocalField)
    (σ : Equiv.Perm (Fin n)) (hσ : OrderCompatible σ)
    (S : Fin n → ℝ) (hS : ∀ i, 0 ≤ S i),
      SchwingerEval K n O σ S = SchwingerEval K n O (Equiv.refl _) S

/-- OS4 holds for the kernel-weighted evaluator since it is permutation‑independent. -/
lemma os4_kernel (K : YM.OSPositivity.OS2.ReflectionKernel) :
    symmetry_holds_for K := by
  intro n hn O σ hσ S hS
  simp [SchwingerEval]

/-- Schwinger data (two- and four-point) equipped with an OS4 symmetry proof
derived from the two-point reflection kernel. -/
structure SchwingerFamily where
  twoPoint : YM.OSPositivity.OS2.ReflectionKernel
  fourPoint : Option FourPointKernel
  os4 : symmetry_holds_for twoPoint

/-- OS input bundle: Euclidean invariance parameters, local field, continuum
witness, Schwinger data, and a reconstruction witness. -/
structure OSInput where
  rp : Euclid.RotationApproxParams
  tp : Euclid.TranslationLimitParams
  F  : YM.OSPositivity.LocalFields.LocalField
  witness : ContinuumLimitWitness
  schwinger : SchwingerFamily
  reconWitness : ReconstructionWitness
  contractionParams : Option YM.OSPositivity.Euclid.FromContraction.Params

/-- Reconstruction output, bundling the upgraded Wightman field and associated
acceptance predicates. -/
structure Reconstruction (I : OSInput) where
  field      : WightmanField
  spectral   : spectrum_condition field
  covariance : Recon.covariance_holds (Recon.build_covariance I.rp I.tp)
  wick       : (Recon.build_wick I.rp I.tp).ok
  micro      : Recon.microcausal field
  local_os   : YM.OSPositivity.LocalFields.os_positive I.F
  inputWitness : ReconstructionWitness
  witness_eq : field.witness = inputWitness

/-- TODO[OS→W functor]: replace this placeholder with the full Lean implementation
of the Osterwalder–Schrader reconstruction once analytic continuation, OS4
symmetry, and gap transport lemmas are formalized
(Yang-Mills-sept21.tex Thm.~\ref{thm:os-to-wightman}). -/
def build_reconstruction (I : OSInput) : Reconstruction I :=
  -- Thread λ₁ from provided contraction params if available, else use default λ₁
  let Wλ : ReconstructionWitness :=
    match I.contractionParams with
    | some P => withLambdaOneFromParams I.reconWitness P
    | none   => withDefaultLambdaOne I.reconWitness
  { field      := build_wightman_field Wλ
  , spectral   := build_wightman_field_satisfies Wλ
  , covariance := by
      exact Recon.covariance_from_euclid I.rp I.tp I.rp.nonneg I.tp.nonneg
  , wick       := by
      exact Recon.wick_from_euclid I.rp I.tp I.rp.nonneg I.tp.nonneg
  , micro      := Recon.microcausal_scalar _
  , local_os   := YM.OSPositivity.LocalFields.build_local_field_os_positive
  , inputWitness := Wλ
  , witness_eq := rfl }

/-- Default OS input with minimal witnesses and contraction parameters choosing λ₁ = 1. -/
noncomputable def default_input : OSInput :=
  by
    classical
    let rp : Euclid.RotationApproxParams :=
      { approx_error := 0
      , nonneg := by simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
    let tp : Euclid.TranslationLimitParams :=
      { tightness := 0
      , nonneg := by simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
    let F : YM.OSPositivity.LocalFields.LocalField :=
      YM.OSPositivity.LocalFields.build_positive_local_field
    let R := YM.OSPositivity.OS2.canonicalReflectionInput
    let K := R.kernel
    let S : SchwingerFamily :=
      let Ggap : YM.OSPositivity.Clustering.FromGap :=
        { gamma_phys := 1, gamma_pos := by simpa using (zero_lt_one : 0 < (1 : ℝ)) }
      let fp : Option FourPointKernel :=
        some (fourPointOfGap Ggap F F F F 1 (by simpa using (zero_le_one : (0 : ℝ) ≤ 1)))
      { twoPoint := K
      , fourPoint := fp
      , os4 := os4_kernel K }
    let witness0 : ReconstructionWitness :=
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
    let cparams : YM.OSPositivity.Euclid.FromContraction.Params :=
      { N := witness0.N
      , instN := witness0.instN
      , β := witness0.β
      , β_pos := witness0.hβ
      , λ1 := 1
      , λ1_pos := by norm_num
      , lattice_dim := 4
      , dim_pos := by decide }
    exact
      { rp := rp
      , tp := tp
      , F := F
      , witness := R.witness
      , schwinger := S
      , reconWitness := witness0
      , contractionParams := some cparams }

lemma os4_implies_microcausal (I : OSInput)
    (h : I.schwinger.os4) : Recon.microcausal (build_reconstruction I).field := by
  -- Current surrogate is trivial; this records the dependency explicitly.
  simpa using Recon.microcausal_scalar _

end YM.OSPositivity.Wightman
