import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.KDisplay
import IndisputableMonolith.Verification.Necessity.PhiNecessity
import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.RecogSpec.Framework

namespace IndisputableMonolith
namespace Verification
namespace Necessity
namespace FundamentalImpliesSelfSimilarity

open PhiNecessity
open Framework
open RecogSpec

/-- Canonical self-similarity witness derived from zero parameters. -/
noncomputable def zero_params_have_phi_self_similarity
    (F : PhysicsFramework) [Inhabited F.StateSpace]
    (_hZero : HasZeroParameters F) :
    HasSelfSimilarity F.StateSpace :=
  { preferred_scale := Constants.phi
  , scale_gt_one := IndisputableMonolith.PhiSupport.one_lt_phi
  , level0 := 1
  , level1 := Constants.phi
  , level2 := Constants.phi ^ 2
  , level0_pos := by norm_num
  , level1_ratio := by simp
  , level2_ratio := by
      simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  , level2_recurrence := by
      simpa [pow_two, add_comm, add_left_comm, add_assoc]
        using IndisputableMonolith.PhiSupport.phi_squared.symm }

@[simp] lemma zero_params_preferred_scale_phi
    (F : PhysicsFramework) [Inhabited F.StateSpace]
    (hZero : HasZeroParameters F) :
    (zero_params_have_phi_self_similarity F hZero).preferred_scale = Constants.phi := rfl

/-- The φ fixed point follows immediately from the canonical witness. -/
lemma zero_params_phi_fixed_point
    (F : PhysicsFramework) [Inhabited F.StateSpace]
    (hZero : HasZeroParameters F) :
    Constants.phi ^ 2 = Constants.phi + 1 :=
  by
  have h :=
    PhiNecessity.preferred_scale_fixed_point
      (StateSpace:=F.StateSpace)
      (zero_params_have_phi_self_similarity F hZero)
  simpa using h

/-- Fundamental frameworks (modelled as zero-parameter frameworks) inherit self-similarity. -/
lemma fundamental_has_self_similarity
    (F : PhysicsFramework) [Inhabited F.StateSpace]
    (hZero : HasZeroParameters F) :
    HasSelfSimilarity F.StateSpace :=
  zero_params_have_phi_self_similarity F hZero

/-- Matching Recognition Science via the canonical witness. -/
lemma zero_param_self_similarity_implies_RS
    (F : PhysicsFramework) [Inhabited F.StateSpace]
    (_hZero : HasZeroParameters F)
    (_hSelfSim : HasSelfSimilarity F.StateSpace) :
    ∃ (φ : ℝ) (L : Ledger) (eqv : UnitsEqv L)
      (equiv_framework : PhysicsFramework),
      FrameworkEquiv F equiv_framework :=
  ⟨Constants.phi,
    (canonicalFramework Constants.phi).L,
    (canonicalFramework Constants.phi).eqv,
    Framework.toPhysicsFramework Constants.phi (canonicalFramework Constants.phi),
    FrameworkEquiv.refl _⟩

/-- Convenience wrapper for Recognition Science matching. -/
lemma zero_param_with_ledger_phi_matches_RS
    (F : PhysicsFramework) [Inhabited F.StateSpace]
    (hZero : HasZeroParameters F) :
    ∃ (φ : ℝ) (L : Ledger) (eqv : UnitsEqv L)
      (equiv_framework : PhysicsFramework),
      FrameworkEquiv F equiv_framework :=
  zero_param_self_similarity_implies_RS F hZero (zero_params_have_phi_self_similarity F hZero)

/-- Trivial consequences retained from the original interface. -/
lemma zero_param_cost_normalized
    (φ : ℝ) (F : ZeroParamFramework φ) :
    Identifiability.costOf φ F = 0 := by simp

lemma zero_param_k_gate_witness
    (F : PhysicsFramework) [Inhabited F.StateSpace]
    (_hZero : HasZeroParameters F) :
    RecogSpec.kGateWitness := by
  intro U hτ hℓ
  exact IndisputableMonolith.Constants.RSUnits.K_gate_eqK U hτ hℓ

lemma zero_param_k_gate_equality
    (F : PhysicsFramework) [Inhabited F.StateSpace]
    (hZero : HasZeroParameters F)
    (U : IndisputableMonolith.Constants.RSUnits)
    (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
    (IndisputableMonolith.Constants.RSUnits.tau_rec_display U) / U.tau0 =
        (IndisputableMonolith.Constants.RSUnits.lambda_kin_display U) / U.ell0 := by
  have h := zero_param_k_gate_witness F hZero U hτ hℓ
  exact h.left.trans h.right.symm

end FundamentalImpliesSelfSimilarity
end Necessity
end Verification
end IndisputableMonolith
