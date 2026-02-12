import IndisputableMonolith.Recognition
import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Verification.Necessity.LedgerNecessity

namespace IndisputableMonolith
namespace Verification
namespace Necessity
namespace ZeroParameter

/-!
# Necessity of Zero Parameters from the Meta-Principle

This module records the foundational axiom that the Meta-Principle enforces a
zero-parameter physics framework. We defer to the shared physics framework
definitions in `Verification.Exclusivity.Framework` to avoid duplicating
infrastructure.
-/

open Verification.Exclusivity

/-! ### MP → algorithmic ledger witness -/

/-- Noncomputable choice of the MP‑constructed ledger.

We choose the ledger produced by `MP_forces_ledger` so we retain a concrete
equivalence with `ℕ` (hence non-emptiness of the carrier). -/
noncomputable def mpLedger (h_mp : Recognition.MP) : RH.RS.Ledger :=
  Classical.choose
    (IndisputableMonolith.Verification.Necessity.LedgerNecessity.MP_forces_ledger
      (E := IndisputableMonolith.Verification.Necessity.LedgerNecessity.mpDiscreteEventSystem)
      (ev := IndisputableMonolith.Verification.Necessity.LedgerNecessity.mpEventEvolution)
      h_mp)

/-- The MP ledger carrier is equivalent to `ℕ` (by construction). -/
theorem mpLedger_equivNat (h_mp : Recognition.MP) :
    Nonempty (ℕ ≃ (mpLedger h_mp).Carrier) :=
  (Classical.choose_spec
    (IndisputableMonolith.Verification.Necessity.LedgerNecessity.MP_forces_ledger
      (E := IndisputableMonolith.Verification.Necessity.LedgerNecessity.mpDiscreteEventSystem)
      (ev := IndisputableMonolith.Verification.Necessity.LedgerNecessity.mpEventEvolution)
      h_mp))

/-- The carrier of `mpLedger h_mp` admits an algorithmic specification. -/
theorem mpLedger_hasAlgorithmicSpec (h_mp : Recognition.MP) :
  Framework.HasAlgorithmicSpec (mpLedger h_mp).Carrier :=
by
  classical
  rcases mpLedger_equivNat h_mp with ⟨e⟩
  exact Framework.HasAlgorithmicSpec.ofEquivNat e

/-- The MP ledger carrier is nonempty. -/
theorem mpLedger_nonempty (h_mp : Recognition.MP) :
    Nonempty (mpLedger h_mp).Carrier := by
  classical
  rcases mpLedger_equivNat h_mp with ⟨e⟩
  exact ⟨e 0⟩

/-- Alias recording the required state-space equivalence to the MP ledger carrier. -/
def MPStateSpaceEquiv (F : Framework.PhysicsFramework) (h_mp : Recognition.MP) :=
  F.StateSpace ≃ (mpLedger h_mp).Carrier

/-- Unified bridge witness from the MP ledger carrier to a framework state space.
    Any surjection suffices; an equivalence is a special case. -/
structure MPBridge (F : Framework.PhysicsFramework) (h_mp : Recognition.MP) where
  toState : (mpLedger h_mp).Carrier → F.StateSpace
  surj : Function.Surjective toState

/-- Build an MP bridge from an explicit state-space equivalence. -/
def MPBridge.ofEquiv
  (F : Framework.PhysicsFramework) (h_mp : Recognition.MP)
  (e : MPStateSpaceEquiv F h_mp) : MPBridge F h_mp :=
{ toState := e.symm
, surj := e.symm.surjective }

/-! Bridging lemma: the explicit equivalence to the MP ledger’s carrier forces zero
    parameters (algorithmic specification) for the framework’s state space. -/
theorem mp_forces_zero_parameters_of_equiv_to_mp_ledger
  (F : Framework.PhysicsFramework) (h_mp : Recognition.MP)
  (e : MPStateSpaceEquiv F h_mp) :
  Framework.HasZeroParameters F := by
  classical
  have hA : Framework.HasAlgorithmicSpec (mpLedger h_mp).Carrier :=
    mpLedger_hasAlgorithmicSpec h_mp
  have hB : Framework.HasAlgorithmicSpec F.StateSpace :=
    Framework.HasAlgorithmicSpec.of_surjective hA e.symm e.symm.surjective
  simpa [Framework.HasZeroParameters] using hB

/-- Bridging lemma via an MP bridge (surjection witness). -/
theorem mp_forces_zero_parameters_of_bridge
  (F : Framework.PhysicsFramework) (h_mp : Recognition.MP)
  (B : MPBridge F h_mp) :
  Framework.HasZeroParameters F := by
  classical
  have hA : Framework.HasAlgorithmicSpec (mpLedger h_mp).Carrier :=
    mpLedger_hasAlgorithmicSpec h_mp
  have hB : Framework.HasAlgorithmicSpec F.StateSpace :=
    Framework.HasAlgorithmicSpec.of_surjective hA B.toState B.surj
  simpa [Framework.HasZeroParameters] using hB

/-- Bridging lemma via a surjection from the MP ledger carrier into the
framework's state space. This relaxes the equivalence requirement; any
surjective map suffices to transport the algorithmic specification. -/
theorem mp_forces_zero_parameters_of_surj_to_mp_ledger
  (F : Framework.PhysicsFramework) (h_mp : Recognition.MP)
  (g : (mpLedger h_mp).Carrier → F.StateSpace)
  (hg : Function.Surjective g) :
  Framework.HasZeroParameters F := by
  classical
  exact
    mp_forces_zero_parameters_of_bridge F h_mp
      { toState := g, surj := hg }

/-! Convenience lemma: by definition, zero parameters means algorithmic. -/
@[simp] theorem has_zero_parameters_iff_algorithmic
  (F : Framework.PhysicsFramework) :
  Framework.HasZeroParameters F ↔
    Framework.HasAlgorithmicSpec F.StateSpace := by
  rfl

end ZeroParameter
end Necessity
end Verification
end IndisputableMonolith
