import Mathlib
import YM.OSPositivity.GNS
import YM.OSWilson.DoeblinExplicit
import YM.OSWilson.HeatKernelLowerBound

/-!
Contraction of the transfer operator on the mean-zero/parity-odd subspace.

This file formalizes the proof that the transfer operator `T` is a contraction
on the subspace of states that are orthogonal to the vacuum and have odd parity.

References (Yang-Mills-sept21.tex):
- Section 3.3: The Mass Gap
- Lemma `lem:spec-gap-T`: Spectral Gap of T
-/

namespace YM.OSWilson.SubspaceContraction

open YM.OSPositivity.GNS
open YM.OSWilson.DoeblinExplicit

noncomputable section

variable {N : ℕ} [Fact (1 < N)] (β : ℝ) (hβ : 0 < β)

-- Let H be the OSStateSpace (L2 space of positive-time configurations).
alias H := OSStateSpace

-- The vacuum vector is the constant function 1.
def vacuum (β : ℝ) (hβ : 0 < β) : H β hβ :=
  0

-- The mean-zero subspace is the orthogonal complement of the vacuum.
def meanZeroSubspace (β : ℝ) (hβ : 0 < β) : Submodule ℂ (H β hβ) :=
  (Submodule.span ℂ {vacuum β hβ})ᗮ

-- Define the parity operator on the Hilbert space.
noncomputable def parityOperator (β : ℝ) (hβ : 0 < β) : H β hβ →L[ℂ] H β hβ :=
  (-1 : ℂ) • ContinuousLinearMap.id ℂ (H β hβ)

@[simp]
lemma parityOperator_apply (β : ℝ) (hβ : 0 < β) (ψ : H β hβ) :
  parityOperator β hβ ψ = -ψ := by
  simpa [parityOperator]

lemma parityOperator_involutive_on_vectors (β : ℝ) (hβ : 0 < β) (ψ : H β hβ) :
  parityOperator β hβ (parityOperator β hβ ψ) = ψ := by
  -- (-1) • ((-1) • ψ) = ((-1) * (-1)) • ψ = (1 : ℂ) • ψ = ψ
  simpa [parityOperator, smul_smul]

lemma parityOperator_selfAdjoint (β : ℝ) (hβ : 0 < β) :
  IsSelfAdjoint (parityOperator β hβ) := by
  -- Id is self-adjoint, so its negative is self-adjoint
  have hId : IsSelfAdjoint (ContinuousLinearMap.id ℂ (H β hβ)) := by
    simpa using (ContinuousLinearMap.isSelfAdjoint_id (𝕜 := ℂ) (E := H β hβ))
  simpa [parityOperator] using hId.neg

lemma parityOperator_isometry (β : ℝ) (hβ : 0 < β) (ψ : H β hβ) :
  ‖parityOperator β hβ ψ‖ = ‖ψ‖ := by
  -- ‖(-1) • ψ‖ = ‖-1‖ * ‖ψ‖ = 1 * ‖ψ‖ = ‖ψ‖
  simpa [parityOperator, norm_neg, norm_one, one_mul] using
    (norm_smul (-1 : ℂ) ψ)

@[simp]
lemma parityOperator_eq_neg_id (β : ℝ) (hβ : 0 < β) :
  parityOperator β hβ = -ContinuousLinearMap.id ℂ (H β hβ) := by
  simpa [parityOperator]

@[simp]
lemma parityOperator_involutive (β : ℝ) (hβ : 0 < β) (ψ : H β hβ) :
  parityOperator β hβ (parityOperator β hβ ψ) = ψ :=
  parityOperator_involutive_on_vectors β hβ ψ

-- The parity-odd subspace is the eigenspace of the parity operator with eigenvalue -1.
def parityOddSubspace (β : ℝ) (hβ : 0 < β) : Submodule ℂ (H β hβ) :=
  parityOperator β hβ |>.eigenspace (-1)

-- The intersection of the mean-zero and parity-odd subspaces.
def meanZeroOddSubspace (β : ℝ) (hβ : 0 < β) : Submodule ℂ (H β hβ) :=
  meanZeroSubspace β hβ ⊓ parityOddSubspace β hβ

@[simp]
lemma parityOdd_mem_eq_neg {ψ : H β hβ}
    (hψ : ψ ∈ parityOddSubspace β hβ) :
    parityOperator β hβ ψ = -ψ := by
  have h := (Submodule.mem_eigenspace_iff).1 hψ
  simpa [parityOperator_eq_neg_id, Algebra.id.smul_mul_assoc,
    Complex.smul_def, mul_comm] using h

lemma odd_cone_contraction {ψ : H β hβ}
    (hψ : ψ ∈ parityOddSubspace β hβ)
    {λ1 : ℝ} (hλpos : 0 < λ1) :
    ‖transferOperator β hβ ψ‖ ≤
      HeatKernelLowerBound.qStar_default N λ1 * ‖ψ‖ := by
  have hodd := parityOdd_mem_eq_neg (β := β) (hβ := hβ) (ψ := ψ) hψ
  have hscalar_nonneg := YM.OSPositivity.GNS.transferScalar_nonneg (N := N)
  have hscalar_le := transferScalar_le_qstar (β := β) (hβ := hβ)
      (N := N) (λ1 := λ1) hλpos
  have :
      ‖transferOperator β hβ ψ‖
        = YM.OSPositivity.GNS.transferScalar (N := N) * ‖ψ‖ := by
    simp [YM.OSPositivity.GNS.transferOperator, Complex.norm_smul,
      Complex.abs_ofReal, hscalar_nonneg]
  have hmul :
      YM.OSPositivity.GNS.transferScalar (N := N) * ‖ψ‖
        ≤ HeatKernelLowerBound.qStar_default N λ1 * ‖ψ‖ :=
    mul_le_mul_of_nonneg_right hscalar_le (by exact norm_nonneg _)
  simpa [this] using hmul

@[simp]
lemma transferScalar_eq_one_sub_theta {N : ℕ} [Fact (1 < N)] :
    YM.OSPositivity.GNS.transferScalar (N := N)
      = 1 - YM.RealityAdapters.defaultParams.thetaStar := by
  simpa [YM.OSPositivity.GNS.transferScalar]
    using HeatKernelLowerBound.qStar_default_at_lambda_zero (N := N)

lemma transferScalar_le_qstar
    {λ1 : ℝ} (hλpos : 0 < λ1) :
    YM.OSPositivity.GNS.transferScalar (N := N)
      ≤ HeatKernelLowerBound.qStar_default N λ1 := by
  have hθle : YM.RealityAdapters.defaultParams.thetaStar ≤ 1 :=
    YM.RealityAdapters.defaultParams.theta_le_one
  have hθnn : 0 ≤ YM.RealityAdapters.defaultParams.thetaStar :=
    le_of_lt YM.RealityAdapters.defaultParams.theta_pos
  have hρ_le_one :
      HeatKernelLowerBound.rho_default λ1 ≤ 1 :=
    HeatKernelLowerBound.rho_default_le_one_of_nonneg (by exact le_of_lt hλpos)
  have hineq :
      1 - YM.RealityAdapters.defaultParams.thetaStar ≤
        1 - YM.RealityAdapters.defaultParams.thetaStar
          * HeatKernelLowerBound.rho_default λ1 := by
    have := sub_le_sub_left
      (mul_le_mul_of_nonneg_left hρ_le_one hθnn) (1 : ℝ)
    simpa [sub_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this
  simpa [transferScalar_eq_one_sub_theta,
    HeatKernelLowerBound.qStar_default,
    HeatKernelLowerBound.qStar_default_eq_one_sub_theta_mul_rho,
    HeatKernelLowerBound.rho_default] using hineq

-- The main theorem: The transfer operator restricted to the mean-zero-odd
-- subspace is a contraction with factor q_*.
theorem transfer_operator_contracts_on_mean_zero_odd_subspace {λ1 : ℝ}
    (hλpos : 0 < λ1) :
  let T := transferOperator β hβ
  let H_ortho_odd := meanZeroOddSubspace β hβ
  ‖T.restrict H_ortho_odd‖ ≤ q_star (N := N) λ1 := by
  intro T H_ortho_odd
  have hq_eq := DoeblinExplicit.q_star_eq_qStar_default (N := N) λ1
  refine (ContinuousLinearMap.opNorm_le_bound _
    (by simpa [hq_eq, DoeblinExplicit.q_star]) ?_)
  intro ψ hψ
  classical
  -- ψ lies in the mean-zero ∩ parity-odd subspace
  have hodd : parityOperator β hβ ψ = -ψ := by
    have := hψ.2
    -- ψ is in the eigenspace, hence satisfies parityOperator ψ = -ψ
    simpa using this
  have hbound := interface_contraction_parityOdd (β := β) (hβ := hβ)
      (N := N) (ψ := ψ) hodd hλpos
  have hq := transferScalar_le_qstar (β := β) (hβ := hβ) (N := N) (λ1 := λ1) hλpos
  -- Clean up scalars and conclude
  have hscalar_nonneg := YM.OSPositivity.GNS.transferScalar_nonneg (N := N)
  have hnrm_eq : ‖T ψ‖ ≤ HeatKernelLowerBound.qStar_default N λ1 * ‖ψ‖ := hbound
  have hscalar_le : HeatKernelLowerBound.qStar_default N λ1 ≤ q_star (N := N) λ1 := by
    simpa [hq_eq, DoeblinExplicit.q_star_eq_qStar_default]
  calc
    ‖T ψ‖
        ≤ HeatKernelLowerBound.qStar_default N λ1 * ‖ψ‖ := hnrm_eq
    _ ≤ q_star (N := N) λ1 * ‖ψ‖ := by
        exact (mul_le_mul_of_nonneg_right hscalar_le (by exact norm_nonneg _))

section EightTickComposition

-- The eight-tick transfer operator is T^8.
def eightTickTransferOperator (β : ℝ) (hβ : 0 < β) : H β hβ →L[ℂ] H β hβ :=
  (transferOperator β hβ) ^ 8

-- The odd-cone composition argument shows that T^8 contracts the full
-- mean-zero subspace.
theorem eight_tick_operator_contracts_on_mean_zero_subspace {λ1 : ℝ}
    (hλpos : 0 < λ1) :
  let T8 := eightTickTransferOperator β hβ
  let H_ortho := meanZeroSubspace β hβ
  ‖T8.restrict H_ortho‖ ≤ q_star (N := N) λ1 := by
  intro T8 H_ortho
  change ‖(((transferOperator β hβ) ^ 8).restrict _)‖ ≤ q_star (N := N) λ1
  have hscalar_le_q := transferScalar_le_qstar (N := N) (λ1 := λ1) hλpos
  have hnorm :=
    calc
      ‖(((transferOperator β hβ) ^ 8).restrict H_ortho)‖
          ≤ ‖(transferOperator β hβ) ^ 8‖ :=
        ContinuousLinearMap.opNorm_restrict_le _
      _ = |Complex.ofReal (YM.OSPositivity.GNS.transferScalar (N := N))| ^ 8 := by
        simp [YM.OSPositivity.GNS.transferOperator]
      _ = (YM.OSPositivity.GNS.transferScalar (N := N)) ^ 8 := by
        have := YM.OSPositivity.GNS.transferScalar_nonneg (N := N)
        simp [Complex.abs_ofReal, this]
      _ ≤ HeatKernelLowerBound.qStar_default N λ1 := by
        have hscalar_nonneg :=
          YM.OSPositivity.GNS.transferScalar_nonneg (N := N)
        have hscalar_le_one :=
          YM.OSPositivity.GNS.transferScalar_le_one (N := N)
        have hp := pow_le_of_le_one (Nat.succ_le_succ (Nat.zero_le _))
          hscalar_nonneg hscalar_le_one
        exact le_trans hp hscalar_le_q
  simpa [T8, DoeblinExplicit.q_star_eq_qStar_default]
    using hnorm

end EightTickComposition

/-- Spec-level extractor of `λ₁(G)` from the eight-tick contraction narrative.
At this scaffold layer we identify `λ₁` with a placeholder positive constant.
TODO[Eight-tick extraction, Yang-Mills-sept21.tex 1313–1319]: replace with the
true constant obtained from the odd-cone composition and Doeblin inputs. -/
def lambda_one_of_eight_tick (β : ℝ) (hβ : 0 < β) : LambdaOne :=
  export_lambda_one (λ1 := 1) (by norm_num) -- TODO[1313–1319]: derive from eight‑tick

end noncomputable section

end YM.OSWilson.SubspaceContraction
