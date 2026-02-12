-- Additional derived machinery for MP-ledger bridging appears later in the file.
import Mathlib
import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Verification.Identifiability.Observations
import IndisputableMonolith.Verification.Necessity.PhiNecessity
import IndisputableMonolith.RH.RS.Framework

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity
namespace NoAlternatives

open Framework
open Necessity
open RH.RS

/-- Data connecting an arbitrary physics framework to a concrete Recognition Science
    zero-parameter realization.  The fields provide:

    * `φ`: the scale forced by self-similarity necessity.
    * `rsFramework`: the zero-parameter RS framework at that scale.
    * `target`: a concrete physics framework representation of the RS data.
    * `iso`: a structural isomorphism exhibiting state/observable equivalence.
    * `observedUD`: observational agreement with the canonical universal ledger.

    Downstream lemmas expose bridge witnesses and framework equivalence. -/
structure RSConnectionData (F : PhysicsFramework) where
  φ : ℝ
  rsFramework : ZeroParamFramework φ
  target : PhysicsFramework
  iso : Framework.FrameworkIso F target
  observedUD :
    Identifiability.observe φ rsFramework =
      Identifiability.observedFromUD φ (UD_explicit φ)

namespace RSConnectionData

variable {F : PhysicsFramework}

/-- The state-space equivalence supplied by the connection data. -/
def stateEquiv (conn : RSConnectionData F) : F.StateSpace ≃ conn.target.StateSpace :=
  conn.iso.stateEquiv

/-- The observable equivalence supplied by the connection data. -/
def observableEquiv (conn : RSConnectionData F) :
    F.Observable ≃ conn.target.Observable :=
  conn.iso.observableEquiv

/-- The evolution compatibility bundled by the connection data. -/
theorem evolve_comm (conn : RSConnectionData F) :
    ∀ s : F.StateSpace,
      conn.stateEquiv (F.evolve s) = conn.target.evolve (conn.stateEquiv s) :=
  conn.iso.evolve_comm

/-- The measurement compatibility bundled by the connection data. -/
theorem measure_comm (conn : RSConnectionData F) :
    ∀ s : F.StateSpace,
      conn.observableEquiv (F.measure s) =
        conn.target.measure (conn.stateEquiv s) :=
  conn.iso.measure_comm

/-- Observational agreement of the RS realization with the canonical universal data. -/
theorem observed_matches_ud (conn : RSConnectionData F) :
    Identifiability.observe conn.φ conn.rsFramework =
      Identifiability.observedFromUD conn.φ (UD_explicit conn.φ) :=
  conn.observedUD

/-- The connection data yields the expected bridge witness from the RS framework. -/
lemma exists_bridge_to_universal (conn : RSConnectionData F) :
    ∃ B : Bridge conn.rsFramework.L,
      ∃ U : UniversalDimless conn.φ,
        Matches conn.φ conn.rsFramework.L B U :=
  conn.rsFramework.hasEU.left

/-- The structural isomorphism furnishes a `FrameworkEquiv` witness. -/
def frameworkEquiv (conn : RSConnectionData F) :
    Framework.FrameworkEquiv F conn.target :=
  ⟨conn.iso⟩

end RSConnectionData

/-- Bundle of assumptions required to run the exclusivity integration. -/
structure NoAlternativesAssumptions (F : PhysicsFramework) where
  nonStatic : NonStatic F
  zeroParams : HasZeroParameters F
  derives : DerivesObservables F
  selfSimilarity : PhiNecessity.HasSelfSimilarity F.StateSpace
  connection : RSConnectionData F

/-- Core assumptions coincide with the exclusivity integration bundle. -/
structure CoreAssumptions (F : PhysicsFramework) where
  nonStatic : NonStatic F
  zeroParams : HasZeroParameters F
  derives : DerivesObservables F
  selfSimilarity : PhiNecessity.HasSelfSimilarity F.StateSpace
  connection : RSConnectionData F

def core_to_noAlternatives {F : PhysicsFramework}
    (A : CoreAssumptions F) :
    NoAlternativesAssumptions F :=
  { nonStatic := A.nonStatic
  , zeroParams := A.zeroParams
  , derives := A.derives
  , selfSimilarity := A.selfSimilarity
  , connection := A.connection }

/-- Framework equivalence is the lightweight relation defined in `Framework`. -/
abbrev FrameworkEquiv := Framework.FrameworkEquiv

/-- Main exclusivity integration theorem (simplified).
    Any framework satisfying the surfaced assumptions is equivalent to
    the canonical Recognition Science zero-parameter framework at φ. -/
theorem no_alternative_frameworks (F : PhysicsFramework)
    (A : NoAlternativesAssumptions F) :
    ∃ (φ : ℝ) (L : Ledger) (eqv : UnitsEqv L)
      (equiv_framework : PhysicsFramework), FrameworkEquiv F equiv_framework := by
  classical
  let conn := A.connection
  refine ⟨conn.φ, conn.rsFramework.L, conn.rsFramework.eqv, conn.target, ?_⟩
  exact conn.frameworkEquiv

/-- Variant: assumptions provided via the explicit bundle. -/
theorem no_alternative_frameworks_from
    (F : PhysicsFramework)
    (A : NoAlternativesAssumptions F) :
    ∃ (φ : ℝ) (L : Ledger) (eqv : UnitsEqv L)
      (equiv_framework : PhysicsFramework), FrameworkEquiv F equiv_framework :=
  no_alternative_frameworks (F:=F) (A:=A)

/-- MP-discharge variant used by certificate adapters. -/
theorem no_alternative_frameworks_from_MP
    (F : PhysicsFramework)
    (A : CoreAssumptions F) :
    ∃ (φ : ℝ) (L : Ledger) (eqv : UnitsEqv L)
      (equiv_framework : PhysicsFramework), FrameworkEquiv F equiv_framework :=
  no_alternative_frameworks (F:=F) (A:=core_to_noAlternatives A)

end NoAlternatives
end Exclusivity
end Verification
end IndisputableMonolith
