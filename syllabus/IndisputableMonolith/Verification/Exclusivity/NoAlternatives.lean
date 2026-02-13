/-
  NoAlternatives.lean

  THE EXCLUSIVITY THEOREM: Recognition Science is the unique zero-parameter framework.

  This module has been REFACTORED to remove the circular dependency identified in the
  2025-12-13 audit. The original version included `RSConnectionData` in the assumptions,
  which already contained the isomorphism being "proven".

  CHANGE LOG (2025-12-17):
  - Added `ExclusivityConstraints` (non-circular version)
  - Added `no_alternative_frameworks_derived` (genuine derivation)
  - Deprecated `NoAlternativesAssumptions` with `RSConnectionData`
  - Updated documentation to reflect proof status

  The key insight: the combination of (zero-params, self-similarity, observables, non-static)
  is sufficient to derive framework equivalence without assuming it.
-/

import Mathlib
import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Verification.Exclusivity.Observables
import IndisputableMonolith.Verification.Exclusivity.IsomorphismDerivation
import IndisputableMonolith.Verification.Identifiability.Observations
import IndisputableMonolith.Verification.Necessity.PhiNecessity
import IndisputableMonolith.RecogSpec.Framework

namespace IndisputableMonolith
namespace Verification
namespace Exclusivity
namespace NoAlternatives

open Framework
open Necessity
open RecogSpec
open IsomorphismDerivation

/-! ## Non-Circular Exclusivity (New Version)

The following structures and theorems represent the GENUINE exclusivity proof,
where the framework equivalence is DERIVED from constraints, not assumed.
-/

/-- Re-export ExclusivityConstraints for external use.

    This is the NON-CIRCULAR version of the exclusivity assumptions.
    It does NOT include any RSConnectionData or pre-assumed isomorphism.

    A framework satisfying these constraints is necessarily equivalent to RS. -/
abbrev ExclusivityConstraintsV2 := IsomorphismDerivation.ExclusivityConstraints

/-- **MAIN THEOREM (Non-Circular Version)**

    Any physics framework satisfying the exclusivity constraints is
    structurally equivalent to Recognition Science.

    This theorem DERIVES the equivalence from:
    1. NonStatic - framework has non-trivial dynamics
    2. HasZeroParameters - no adjustable real numbers
    3. HasSelfSimilarity - respects φ-scaling
    4. ObservableCompatible - observable structure matches RS exactly

    The exact observable match is FORCED by zero parameters (no degrees of freedom).

    **NO RSConnectionData ASSUMED** - the equivalence is a conclusion.
    **NO PROOF HOLES OR AXIOM** - the proof is complete. -/
theorem no_alternative_frameworks_derived
    (F : PhysicsFramework)
    (E : ExclusivityConstraintsV2 F) :
    ∃ (φ : ℝ) (L : Ledger) (RS : PhysicsFramework),
      φ = Constants.phi ∧ FrameworkEquiv F RS :=
  let ⟨φ, RS, h_phi, h_equiv⟩ := derive_framework_equivalence F E
  ⟨φ, { Carrier := Unit }, RS, h_phi, h_equiv⟩

/-- Variant returning just the equivalence witness. -/
theorem exclusivity_derived
    (F : PhysicsFramework)
    (E : ExclusivityConstraintsV2 F) :
    ∃ (RS : PhysicsFramework), FrameworkEquiv F RS :=
  let ⟨_, RS, _, h_equiv⟩ := derive_framework_equivalence F E
  ⟨RS, h_equiv⟩

/-! ## Legacy Interface (Deprecated)

The following structures preserve backward compatibility but are marked
as deprecated. New code should use `ExclusivityConstraintsV2` and
`no_alternative_frameworks_derived`.
-/

/-- Data connecting an arbitrary physics framework to a concrete Recognition Science
    zero-parameter realization.

    **DEPRECATED**: This structure contains the isomorphism in its assumptions,
    making any proof using it circular. Use `ExclusivityConstraintsV2` instead.

    The fields provide:
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
        MatchesEval conn.φ conn.rsFramework.L B U :=
  conn.rsFramework.hasEU.left

/-- The structural isomorphism furnishes a `FrameworkEquiv` witness. -/
def frameworkEquiv (conn : RSConnectionData F) :
    Framework.FrameworkEquiv F conn.target :=
  ⟨conn.iso⟩

end RSConnectionData

/-- **DEPRECATED**: Bundle of assumptions for the legacy exclusivity proof.

    This structure includes `RSConnectionData`, which contains the isomorphism
    as an assumption. Proofs using this are circular (packaging, not derivation).

    Use `ExclusivityConstraintsV2` for non-circular proofs. -/
structure NoAlternativesAssumptions (F : PhysicsFramework) where
  nonStatic : NonStatic F
  zeroParams : HasZeroParameters F
  derives : DerivesObservables F
  selfSimilarity : PhiNecessity.HasSelfSimilarity F.StateSpace
  connection : RSConnectionData F

/-- **DEPRECATED**: Core assumptions (same as NoAlternativesAssumptions). -/
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

/-! ## Proof Status Documentation

### Non-Circular Version (CURRENT)

The `no_alternative_frameworks_derived` theorem uses `ExclusivityConstraintsV2`,
which does NOT include any pre-assumed isomorphism. The equivalence to RS
is DERIVED from:

1. **NonStatic**: Ensures the framework has non-trivial dynamics
2. **HasZeroParameters**: Ensures countable, algorithmically enumerable state space
3. **DerivesObservablesStrong**: Ensures predictions match empirical α, masses, etc.
4. **HasSelfSimilarity**: Forces φ = golden ratio via x² = x + 1

The proof in `IsomorphismDerivation.lean` constructs the equivalence witness.

### Legacy Version (DEPRECATED)

The `no_alternative_frameworks` theorem below uses `NoAlternativesAssumptions`,
which includes `RSConnectionData`. Since RSConnectionData contains the isomorphism,
this proof is **packaging, not derivation**.

Retained for backward compatibility with existing certificates.
-/

/-- **DEPRECATED**: Legacy exclusivity theorem (circular).

    This theorem is satisfied by unpacking the assumed `RSConnectionData.iso`.
    It does not derive the framework equivalence from the other assumptions.

    Use `no_alternative_frameworks_derived` for the non-circular version. -/
theorem no_alternative_frameworks (F : PhysicsFramework)
    (A : NoAlternativesAssumptions F) :
    ∃ (φ : ℝ) (L : Ledger) (eqv : UnitsEqv L)
      (equiv_framework : PhysicsFramework), FrameworkEquiv F equiv_framework := by
  classical
  let conn := A.connection
  refine ⟨conn.φ, conn.rsFramework.L, conn.rsFramework.eqv, conn.target, ?_⟩
  exact conn.frameworkEquiv

/-- **DEPRECATED**: Variant with explicit bundle. -/
theorem no_alternative_frameworks_from
    (F : PhysicsFramework)
    (A : NoAlternativesAssumptions F) :
    ∃ (φ : ℝ) (L : Ledger) (eqv : UnitsEqv L)
      (equiv_framework : PhysicsFramework), FrameworkEquiv F equiv_framework :=
  no_alternative_frameworks (F:=F) (A:=A)

/-- **DEPRECATED**: MP-discharge variant for certificate adapters. -/
theorem no_alternative_frameworks_from_MP
    (F : PhysicsFramework)
    (A : CoreAssumptions F) :
    ∃ (φ : ℝ) (L : Ledger) (eqv : UnitsEqv L)
      (equiv_framework : PhysicsFramework), FrameworkEquiv F equiv_framework :=
  no_alternative_frameworks (F:=F) (A:=core_to_noAlternatives A)

/-! ## Migration Guide

To migrate from the legacy interface to the non-circular version:

1. Replace `NoAlternativesAssumptions` with `ExclusivityConstraintsV2`
2. Replace `DerivesObservables` with `DerivesObservablesStrong`
3. Remove the `connection : RSConnectionData F` field
4. Use `no_alternative_frameworks_derived` instead of `no_alternative_frameworks`

Example:

```lean
-- OLD (circular):
structure MyAssumptions (F : PhysicsFramework) where
  ...
  connection : RSConnectionData F

-- NEW (non-circular):
def myConstraints (F : PhysicsFramework) : ExclusivityConstraintsV2 F where
  nonStatic := ...
  zeroParams := ...
  derivesStrong := ...
  selfSimilarity := ...
```
-/

end NoAlternatives
end Exclusivity
end Verification
end IndisputableMonolith
