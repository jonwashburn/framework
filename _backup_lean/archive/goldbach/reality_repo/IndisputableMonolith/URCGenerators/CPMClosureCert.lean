import Mathlib
import IndisputableMonolith.CPM.LawOfExistence
import IndisputableMonolith.Verification.CPMBridge.Domain.Hodge
import IndisputableMonolith.Verification.CPMBridge.Domain.RH
import IndisputableMonolith.Verification.CPMBridge.Domain.NavierStokes
import IndisputableMonolith.Verification.CPMBridge.Domain.Goldbach

namespace IndisputableMonolith
namespace URCGenerators

/-!
# CPM Closure Certificate

Certificate asserting CPM core (A/B/C-style) consequences are available
across all four domain scaffolds (Hodge, RH, Navier–Stokes, Goldbach)
and that the RS core constants witness (Knet=1, Cproj=2) is present.

This is #eval-friendly via a URC adapter.
-/

open IndisputableMonolith.CPM.LawOfExistence
open IndisputableMonolith.Verification.CPMBridge

/-- Certificate for CPM closure across domains. -/
structure CPMClosureCert where
  deriving Repr

/-- Verification predicate for CPM closure certificate.

Asserts coercivity (B), aggregation (C), and positive cmin hold for
each domain scaffold, and that RS core constants (Knet=1, Cproj=2)
are witnessed. -/
@[simp] def CPMClosureCert.verified (_c : CPMClosureCert) : Prop :=
  let K1 := IndisputableMonolith.CPM.LawOfExistence.RS.coneConstants.Knet = 1
  let P2 := IndisputableMonolith.CPM.LawOfExistence.RS.coneConstants.Cproj = 2
  K1 ∧ P2 ∧
  (∀ {β} (A : Domain.Hodge.Assumptions β) (a : β),
    let M := Domain.Hodge.Assumptions.model A;
    (M.energyGap a ≥ cmin M.C * M.defectMass a) ∧
    (M.defectMass a ≤ (M.C.Knet * M.C.Cproj * M.C.Cdisp) * M.tests a) ∧
    (0 < cmin M.C)) ∧
  (∀ {β} (A : Domain.RH.Assumptions β) (a : β),
    let M := Domain.RH.Assumptions.model A;
    (M.energyGap a ≥ cmin M.C * M.defectMass a) ∧
    (M.defectMass a ≤ (M.C.Knet * M.C.Cproj * M.C.Cdisp) * M.tests a) ∧
    (0 < cmin M.C)) ∧
  (∀ {β} (A : Domain.NavierStokes.Assumptions β) (a : β),
    let M := Domain.NavierStokes.Assumptions.model A;
    (M.energyGap a ≥ cmin M.C * M.defectMass a) ∧
    (M.defectMass a ≤ (M.C.Knet * M.C.Cproj * M.C.Cdisp) * M.tests a) ∧
    (0 < cmin M.C)) ∧
  (∀ {β} (A : Domain.Goldbach.Assumptions β) (a : β),
    let M := Domain.Goldbach.Assumptions.model A;
    (M.energyGap a ≥ cmin M.C * M.defectMass a) ∧
    (M.defectMass a ≤ (M.C.Knet * M.C.Cproj * M.C.Cdisp) * M.tests a) ∧
    (0 < cmin M.C))

/-- Top-level theorem: CPM closure certificate verifies. -/
@[simp] theorem CPMClosureCert.verified_any (c : CPMClosureCert) :
  CPMClosureCert.verified c := by
  -- Unpack RS core witness trivially
  dsimp [CPMClosureCert.verified]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro β A a;
    -- Hodge domain: use exported theorems
    have hB := Domain.Hodge.Assumptions.coercivity (A:=A) a
    have hC := Domain.Hodge.Assumptions.aggregation (A:=A) a
    have hP := Domain.Hodge.Assumptions.cmin_pos (A:=A)
    exact And.intro hB (And.intro hC hP)
  constructor
  · intro β A a;
    have hB := Domain.RH.Assumptions.coercivity (A:=A) a
    have hC := Domain.RH.Assumptions.aggregation (A:=A) a
    have hP := Domain.RH.Assumptions.cmin_pos (A:=A)
    exact And.intro hB (And.intro hC hP)
  constructor
  · intro β A a;
    have hB := Domain.NavierStokes.Assumptions.coercivity (A:=A) a
    have hC := Domain.NavierStokes.Assumptions.aggregation (A:=A) a
    have hP := Domain.NavierStokes.Assumptions.cmin_pos (A:=A)
    exact And.intro hB (And.intro hC hP)
  · intro β A a;
    have hB := Domain.Goldbach.Assumptions.coercivity (A:=A) a
    have hC := Domain.Goldbach.Assumptions.aggregation (A:=A) a
    have hP := Domain.Goldbach.Assumptions.cmin_pos (A:=A)
    exact And.intro hB (And.intro hC hP)

end URCGenerators
end IndisputableMonolith
