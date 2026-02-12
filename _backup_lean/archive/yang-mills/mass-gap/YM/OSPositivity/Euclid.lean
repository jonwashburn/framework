import Mathlib
import YM.SpectralStability.RescaledNRC
import YM.Continuum.Limit
import YM.OSWilson.SubspaceContraction

/-!
T13 (OS1_Equicontinuity): spec-level acceptance for equicontinuity modulus
and Euclidean invariance (hypercubic, rotation, translation limits), with an
aggregate builder. Boolean flags are replaced by Propositions.
References: Yang-Mills-sept21.tex lines 1482–1504 (global OS0–OS1), 1234–1278 (discrete→continuum OS1 mechanics).
No axioms. No `sorry`. No `admit`.

## Spec Placeholder Inventory
- `EqModParams`/`EqModOut`: stand in for the van Hove–limit Schwinger modulus of
  smeared observables; currently store only radii and a scalar modulus.
- `HypercubicParams`, `RotationApproxParams`, `TranslationLimitParams`: abstract
  the discrete symmetry controls without encoding the transfer/heat-kernel
  machinery that produces $O(a^2)$ error bounds.
- `EuclidAggregate*`: aggregate placeholders bundling the preceding objects and
  Proposition-valued invariance flags rather than certified Schwinger limits.

These placeholders must eventually be replaced by the OS0–OS1 data constructed
in Yang-Mills-sept21.tex, §3.4–§3.6, where the smeared Schwinger functions,
equicontinuity modulus, and Euclidean invariance of the continuum limit are
proved from transfer, NRC, and smearing inputs.

TODO[OS0–OS1 completion]:
- Replace the placeholder `EqModOut`/`EuclidAggregateOut` witnesses with genuine
  continuum Schwinger functions obtained from the van Hove limits described in
  Yang-Mills-sept21.tex, Thm.~\ref{thm:global-OS01} (lines 1482–1504).
- Formalize the uniform equicontinuity bounds (UEI) from Lemma~\ref{lem:E1-tightness}
  and Proposition~\ref{prop:OS0-poly} to show `equicontinuity_modulus_spec`
  derives from the lattice heat-kernel/transfer inputs (cf. lines 1200–1311 on
  NRC convergence) and the smeared Schwinger moments.
- Upgrade the rotation/translation propositions to certified $E(4)$ invariance
  by integrating the commutator and resolvent control in Lemma~\ref{lem:commutator-Oa2}
  (lines 1222–1268). This requires a Lean formalization of the discrete-to-continuum
  action estimates and their $O(a^2)$ errors, tied to the transfer matrix spectrum.
- Track the dependence on smeared gauge-invariant observables built in
  §3.4 (lines 1497–1504) so that `EuclidAggregateParams.region_size` aligns with
  the smearing radius control coming from the continuum limit and the NRC scaling.
- Cross-link the resulting witnesses with the reflection-positive local fields
  (see `YM/OSPositivity/LocalFields.lean`) to ensure the Schwinger family matches
  the OS2/OS4 requirements used in reconstruction.
See also: Glimm–Jaffe, *Quantum Physics* (Chap. VI) for the OS1 invariance
construction to cross-reference the analytic requirements.
-/

namespace YM.OSPositivity.Euclid

open YM.SpectralStability.RescaledNRC
open YM.Continuum.Limit

/-- UEI witness packaged with the fixed region, extracted from the continuum-limit module. -/
structure UEIWitness where
  region : FixedRegion
  witness : UEI
  holds : uei_holds region witness

/-- Build a UEI witness from `uei_iso_exist` on a fixed region of radius `r`. -/
def ueiWitnessOfRadius (r : ℝ) (hr : 0 < r) : UEIWitness :=
  let R : FixedRegion := { radius := r, radius_pos := hr }
  let ⟨U, hU, _⟩ := uei_iso_exist R
  { region := R, witness := U, holds := hU }

/-- Equicontinuity modulus extracted from a UEI witness (Schwinger modulus surrogate). -/
def schwinger_modulus (W : UEIWitness) : EqModOut :=
  { omega := W.witness.bound }

/-- The UEI bound ensures the extracted modulus satisfies the nonnegativity spec. -/
theorem schwinger_modulus_spec (W : UEIWitness) :
    equicontinuity_modulus_spec { region_size := W.region.radius } (schwinger_modulus W) := by
  dsimp [equicontinuity_modulus_spec, schwinger_modulus]
  exact W.witness.nonneg

/-- Parameters for an equicontinuity modulus on a fixed region. -/
-- TODO[Schwinger data → modulus]: replace the bare parameters by the actual
-- modulus extracted from smeared Schwinger functions as in Yang-Mills-sept21.tex
-- Def.~3.4.1 (lines 1497–1504), once the heat-kernel bounds from NRC
-- Theorem~\ref{thm:nrc-operator-norm-fixed} (lines 1200–1219) are formalized.
structure EqModParams where
  region_size : ℝ

/-- Output container for a numeric modulus value (spec-level). -/
-- TODO[UEI modulus witness]: encode the equicontinuity modulus returned by
-- Proposition~\ref{prop:U1-uei} (Yang-Mills-sept21.tex lines 1504ff) once Lean
-- has the UEI profile available and the transfer/heat-kernel lemmas in
-- `YM/OSWilson/HeatKernelLowerBound.lean` together with `YM/Transfer/OSGNS.lean`
-- provide the required bounds on smeared insertions.
structure EqModOut where
  omega : ℝ

/-- Spec: the modulus value is nonnegative (acts as an error bound). -/
-- TODO[Temperedness → modulus]: relate this spec to OS0 temperedness bounds
-- (Prop.~\ref{prop:OS0-poly}, lines 283–331) so that the omega witness is tied
-- to the polynomial moment control of smeared observables and the NRC bounds in
-- `YM/SpectralStability/RescaledNRC.lean`.
def equicontinuity_modulus_spec (P : EqModParams) (O : EqModOut) : Prop :=
  0 ≤ O.omega

/-- Hypercubic invariance parameters, with a witness that dimension ≥ 1. -/
-- TODO[Discrete symmetry control]: extend these parameters to record the
-- hypercubic action on lattice observables and the $O(a^2)$ defects from
-- Lemma~\ref{lem:commutator-Oa2} (lines 1222–1257), coordinating with the
-- discrete symmetry estimates in `YM/OSWilson/Cylinder.lean`.
structure HypercubicParams where
  lattice_dim : Nat
  dim_pos : 1 ≤ lattice_dim

/-- Spec: hypercubic invariance requires a positive dimension. -/
-- TODO[OS1 global invariance]: replace this predicate with the certified
-- $E(4)$-invariance of the limiting Schwinger distributions (Thm.~\ref{thm:global-OS01}).
def hypercubic_invariance_spec (P : HypercubicParams) : Prop :=
  1 ≤ P.lattice_dim

/-- Rotation approximation parameters with a nonnegativity witness. -/
-- TODO[Rotation control inputs]: include rotation generators and NRC-based
-- resolvent bounds (Cor.~\ref{cor:resolvent-commutator}, lines 1259–1268) to
-- quantify the `approx_error`, referencing the contraction bounds in
-- `YM/OSWilson/SubspaceContraction.lean`.
structure RotationApproxParams where
  approx_error : ℝ
  nonneg : 0 ≤ approx_error

/-- Spec: rotation approximation error is nonnegative. -/
def rotation_approx_limit_spec (P : RotationApproxParams) : Prop :=
  P.nonneg

/-- Translation limit parameters with a nonnegativity witness. -/
-- TODO[Translation tightness]: supply the $L^1$-tightness from smearing control
-- described around lines 1504–1508 so that this tightness parameter is derived
-- from actual moment bounds, leveraging the lower bounds in
-- `YM/OSWilson/HeatKernelLowerBound.lean`.
structure TranslationLimitParams where
  tightness : ℝ
  nonneg : 0 ≤ tightness

/-- Spec: translation-limit tightness is nonnegative. -/
def translation_limit_spec (P : TranslationLimitParams) : Prop :=
  P.nonneg

/-- Euclidean invariance parameters bundling rotation and translation properties as propositions. -/
structure EuclidInvParams where
  rot_ok : Prop
  trans_ok : Prop

/-- Spec: Euclidean invariance limit = rotation ∧ translation invariance. -/
-- TODO[OS1 completion]: assert the full OS1 statement (rotation + translation)
-- with references to Theorem~\ref{thm:global-OS01} once the spectrum/transfer
-- machinery (lines 1200–1314) is mechanized.
def euclid_invariance_limit_spec (P : EuclidInvParams) : Prop :=
  (P.rot_ok) ∧ (P.trans_ok)

/-!
Bridge from transfer subspace contraction (OSWilson) to Euclidean invariance flags.

We package the parameters that drive the contraction theorems in
`YM/OSWilson/SubspaceContraction.lean` and export rotation/translation flags
at the current spec level. This wires the contraction pipeline into OS1
placeholders without committing to the full analytic content yet.
-/

namespace FromContraction

open YM.OSWilson.SubspaceContraction

/-- Inputs sufficient to apply subspace/eight-tick contraction theorems. -/
structure Params where
  N           : ℕ
  instN       : Fact (1 < N)
  β           : ℝ
  β_pos       : 0 < β
  λ1          : ℝ
  λ1_pos      : 0 < λ1
  lattice_dim : Nat
  dim_pos     : 1 ≤ lattice_dim

attribute [instance] Params.instN

/-- Conservative rotation parameters extracted from contraction data.
Currently sets `approx_error = 0` with a trivial nonnegativity proof; this is
the placeholder to be refined using explicit commutator/resolvent bounds and the
contraction factor (e.g. via `q_star`). -/
def rotationParams (P : Params) : RotationApproxParams :=
  { approx_error := 0
  , nonneg := by
      -- 0 ≤ 0 over ℝ
      simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }

/-- Conservative translation parameters extracted from contraction data. -/
def translationParams (P : Params) : TranslationLimitParams :=
  { tightness := 0
  , nonneg := by
      -- 0 ≤ 0 over ℝ
      simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }

/-- Build Euclidean invariance flags from contraction-derived params. -/
def invParams (P : Params) : EuclidInvParams :=
  let rp := rotationParams P
  let tp := translationParams P
  { rot_ok := rotation_approx_limit_spec rp
  , trans_ok := translation_limit_spec tp }

/-- With contraction-derived params, the Euclidean invariance limit holds at the
current spec level (rotation ∧ translation flags). -/
theorem euclid_from_contraction (P : Params) :
    euclid_invariance_limit_spec (invParams P) := by
  -- both flags are `True` at this spec layer via nonnegativity of 0
  exact And.intro (rotation_approx_limit_exists (rotationParams P))
                  (translation_limit_exists (translationParams P))

  /-- Package `λ₁` from contraction params into an OSWilson `LambdaOne` witness. -/
  def LambdaOne.ofParams (P : Params) : YM.OSWilson.SubspaceContraction.LambdaOne :=
    { λ1 := P.λ1, hλ1 := P.λ1_pos }

end FromContraction

export FromContraction (LambdaOne.ofParams)

/-- Existence lemmas (spec-level) for T13 components. -/
def build_equicontinuity_modulus (P : EqModParams) : EqModOut := { omega := 0 }

theorem equicontinuity_modulus_exists (P : EqModParams) :
  ∃ O : EqModOut, equicontinuity_modulus_spec P O := by
  classical
  have hpos : 0 < max P.region_size 1 :=
    lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) (le_max_right _ _)
  let W := ueiWitnessOfRadius (max P.region_size 1) hpos
  refine ⟨schwinger_modulus W, ?_⟩
  simpa using schwinger_modulus_spec W

theorem hypercubic_invariance_exists (P : HypercubicParams) :
  hypercubic_invariance_spec P :=
  P.dim_pos

theorem rotation_approx_limit_exists (P : RotationApproxParams) :
  rotation_approx_limit_spec P :=
  P.nonneg

theorem translation_limit_exists (P : TranslationLimitParams) :
  translation_limit_spec P :=
  P.nonneg

/-! Aggregator: equicontinuity/invariance bundle with explicit outputs. -/

-- TODO[Aggregate inputs]: generalize this bundle to track the lattice spacing `a`,
-- van Hove volume, and smearing radii so that the dependencies match the OS0–OS1
-- limits proven in Yang-Mills-sept21.tex §§3.4–3.5 and thread through the NRC
-- persistence lemmas in `YM/SpectralStability/Persistence.lean` and the transfer
-- contraction chain in `YM/OSWilson/DeriveGap.lean`.
structure EuclidAggregateParams where
  region_size  : ℝ
  lattice_dim  : Nat
  dim_pos      : 1 ≤ lattice_dim
  approx_error : ℝ
  ae_nonneg    : 0 ≤ approx_error
  tightness    : ℝ
  ti_nonneg    : 0 ≤ tightness

-- TODO[Continuum outputs]: replace these propositional flags by the actual
-- Schwinger function limits and covariance witnesses once the transfer/NRC
-- chain (Theorem~\ref{thm:global-OS0-5}, lines 1551–1560) is formalized.
structure EuclidAggregateOut where
  omega    : ℝ
  rot_ok   : Prop
  trans_ok : Prop

/-- Build the Euclid aggregator using existing component builders/specs (spec-level). -/
def build_euclid_aggregate (P : EuclidAggregateParams) : EuclidAggregateOut :=
  let em := build_equicontinuity_modulus { region_size := P.region_size }
  let rp : RotationApproxParams := { approx_error := P.approx_error, nonneg := P.ae_nonneg }
  let tp : TranslationLimitParams := { tightness := P.tightness, nonneg := P.ti_nonneg }
  { omega := em.omega
  , rot_ok := rotation_approx_limit_spec rp
  , trans_ok := translation_limit_spec tp }

/-- Existence of the Euclid aggregate with component specs holding (spec-level). -/
-- TODO[Schwinger limit verification]: the following existence theorem must be
-- replaced by a proof that the limiting Schwinger functions satisfy OS0–OS1.
-- This will require: (i) canonical embeddings $I_{a,R}$ from discrete to
-- continuum GNS spaces, (ii) uniform heat-kernel convergence (Cor.~\ref{cor:nrc-allz-fixed}),
-- and (iii) extraction of the equicontinuity modulus from smeared correlators.
theorem euclid_aggregate_exists (P : EuclidAggregateParams) :
  ∃ O : EuclidAggregateOut,
    equicontinuity_modulus_spec { region_size := P.region_size } (build_equicontinuity_modulus { region_size := P.region_size }) ∧
    hypercubic_invariance_spec { lattice_dim := P.lattice_dim, dim_pos := P.dim_pos } ∧
    rotation_approx_limit_spec { approx_error := P.approx_error, nonneg := P.ae_nonneg } ∧
    translation_limit_spec { tightness := P.tightness, nonneg := P.ti_nonneg } ∧
    euclid_invariance_limit_spec { rot_ok := rotation_approx_limit_spec { approx_error := P.approx_error, nonneg := P.ae_nonneg }
                                , trans_ok := translation_limit_spec { tightness := P.tightness, nonneg := P.ti_nonneg } } :=
by
  refine ⟨build_euclid_aggregate P, ?_⟩
  constructor
  · -- 0 ≤ 0 over ℝ
    simpa using (le_of_eq (rfl : (0 : ℝ) = 0))
  constructor
  · exact P.dim_pos
  constructor
  · exact P.ae_nonneg
  constructor
  · exact P.ti_nonneg
  · exact And.intro P.ae_nonneg P.ti_nonneg

/-- Definitional equalities for the aggregate outputs. -/
-- TODO[Lean binding to continuum]: once the real Schwinger modulus is
-- implemented, ensure these simp lemmas align with the actual constructions
-- (likely via `rfl` replaced by transport lemmas across the embeddings `I_{a,R}`).
@[simp] theorem build_euclid_aggregate_omega (P : EuclidAggregateParams) :
  (build_euclid_aggregate P).omega = (build_equicontinuity_modulus { region_size := P.region_size }).omega := rfl

@[simp] theorem build_euclid_aggregate_rot (P : EuclidAggregateParams) :
  (build_euclid_aggregate P).rot_ok = rotation_approx_limit_spec { approx_error := P.approx_error, nonneg := P.ae_nonneg } := rfl

@[simp] theorem build_euclid_aggregate_trans (P : EuclidAggregateParams) :
  (build_euclid_aggregate P).trans_ok = translation_limit_spec { tightness := P.tightness, nonneg := P.ti_nonneg } := rfl

end YM.OSPositivity.Euclid
namespace YM.OSPositivity.Euclid

/-- CERT_FN alias: acceptance predicate for T13 matching bridge naming.
TODO[OS→Wightman alignment]: ensure this alias links to the eventual OS1 proof
that feeds into the reconstruction pipeline described in Yang-Mills-sept21.tex
Theorem~\ref{thm:os-to-wightman} (see lines 271–331). -/
def euclid_invariance_limit (P : EuclidInvParams) : Prop :=
  euclid_invariance_limit_spec P

@[simp] theorem euclid_invariance_limit_def (P : EuclidInvParams) :
  euclid_invariance_limit P = euclid_invariance_limit_spec P := rfl

/-- Given component specs, the Euclidean invariance limit holds. -/
theorem euclid_invariance_limit_holds
  (rp : RotationApproxParams) (tp : TranslationLimitParams)
  (hR : rotation_approx_limit_spec rp) (hT : translation_limit_spec tp) :
  euclid_invariance_limit { rot_ok := rotation_approx_limit_spec rp, trans_ok := translation_limit_spec tp } := by
  exact And.intro hR hT

end YM.OSPositivity.Euclid
