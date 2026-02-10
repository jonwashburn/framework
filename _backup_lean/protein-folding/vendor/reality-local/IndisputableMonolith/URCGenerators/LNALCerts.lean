import Mathlib
import IndisputableMonolith.LNAL.Compiler
import IndisputableMonolith.LNAL.Parser
import IndisputableMonolith.LNAL.Invariants
import IndisputableMonolith.LNAL.VM
import IndisputableMonolith.Certificates.JMonotone
import IndisputableMonolith.Certificates.UnitsKGate

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith.LNAL

/-- LNAL invariants certificate: bundles VM preservation and token δ‑unit bound. -/
structure LNALInvariantsCert where
  ok     : Bool
  errors : List String := []
deriving Repr

@[simp] def LNALInvariantsCert.verified (_c : LNALInvariantsCert) : Prop :=
  -- 1) VMInvariant preserved by one small-step
  (∀ (P : IndisputableMonolith.LNAL.LProgram)
     (s : IndisputableMonolith.LNAL.LState),
      IndisputableMonolith.LNAL.VMInvariant s →
      IndisputableMonolith.LNAL.VMInvariant (IndisputableMonolith.LNAL.lStep P s))
  ∧
  -- 2) Token parity implies |ΔtokenCt| ≤ 1 per step
  (∀ (P : IndisputableMonolith.LNAL.LProgram)
     (s : IndisputableMonolith.LNAL.LState),
      IndisputableMonolith.LNAL.TokenParityInvariant s →
      IndisputableMonolith.LNAL.DeltaUnit s.aux5.tokenCt
        (IndisputableMonolith.LNAL.lStep P s).aux5.tokenCt)

@[simp] theorem LNALInvariantsCert.verified_any (c : LNALInvariantsCert) :
  LNALInvariantsCert.verified c := by
  constructor
  · intro P s h; simpa using
      (IndisputableMonolith.LNAL.lStep_preserves_VMInvariant (P:=P) (s:=s) h)
  · intro P s h; simpa using
      (IndisputableMonolith.LNAL.token_delta_unit (P:=P) (s:=s) h)

def LNALInvariantsCert.fromSource (src : String) : LNALInvariantsCert :=
  let parsed := parseProgramFull src
  let emptyPhi : PhiIR.PhiAnalysis := { literals := #[], errors := #[], duplicateNames := [] }
  let emptyPackets : PhiIR.PacketAnalysis := {}
  let code := match parsed with
    | .ok out => out.code
    | .error _ => #[]
  let phi := match parsed with
    | .ok out => out.phi
    | .error _ => emptyPhi
  let packets := match parsed with
    | .ok out => out.packets
    | .error _ => emptyPackets
  let rep := staticChecks code phi packets
  { ok := rep.ok, errors := rep.errors }

/-- Certificate stub for compiler checks (identical to invariants for now). -/
structure CompilerChecksCert where
  ok     : Bool
  errors : List String := []
deriving Repr

@[simp] def CompilerChecksCert.verified (c : CompilerChecksCert) : Prop := c.ok = true

def CompilerChecksCert.fromSource (src : String) : CompilerChecksCert :=
  let parsed := parseProgramFull src
  let emptyPhi : PhiIR.PhiAnalysis := { literals := #[], errors := #[], duplicateNames := [] }
  let emptyPackets : PhiIR.PacketAnalysis := {}
  let code := match parsed with
    | .ok out => out.code
    | .error _ => #[]
  let phi := match parsed with
    | .ok out => out.phi
    | .error _ => emptyPhi
  let packets := match parsed with
    | .ok out => out.packets
    | .error _ => emptyPackets
  let rep := staticChecks code phi packets
  { ok := rep.ok, errors := rep.errors }

/-- Opcode soundness certificate (parsing validates opcode set). -/
structure OpcodeSoundnessCert where deriving Repr

/-- Parser covers all VM opcodes by name. -/
@[simp] def OpcodeSoundnessCert.verified (_c : OpcodeSoundnessCert) : Prop :=
  ∀ (op : IndisputableMonolith.LNAL.Opcode),
    ∃ s : String, IndisputableMonolith.LNAL.parseOpcode s = some op

@[simp] theorem OpcodeSoundnessCert.verified_any (c : OpcodeSoundnessCert) :
  OpcodeSoundnessCert.verified c := by
  intro op; cases op <;> first
    | exact ⟨"LOCK", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"BALANCE", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"FOLD", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"UNFOLD", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"BRAID", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"HARDEN", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"SEED", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"SPAWN", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"MERGE", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"LISTEN", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"GIVE", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"REGIVE", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"FLIP", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"VECTOR_EQ", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"CYCLE", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩
    | exact ⟨"GC_SEED", by simp [IndisputableMonolith.LNAL.parseOpcode]⟩

def OpcodeSoundnessCert.fromSource (_src : String) : OpcodeSoundnessCert :=
  {}

/-- Schedule neutrality certificate aggregating schedule-related checks. -/
structure ScheduleNeutralityCert where
  ok     : Bool
  errors : List String := []
deriving Repr

@[simp] def ScheduleNeutralityCert.verified (_c : ScheduleNeutralityCert) : Prop :=
  ∀ (P : IndisputableMonolith.LNAL.LProgram)
    (s : IndisputableMonolith.LNAL.LState),
    IndisputableMonolith.LNAL.EightTickInvariant P s →
    ∃ r, r ≤ 7 ∧ ∀ k,
      (Function.iterate (IndisputableMonolith.LNAL.lStep P) (r + 8 * k) s).winIdx8 = 0 ∧
      (Function.iterate (IndisputableMonolith.LNAL.lStep P) (r + 8 * k) s).winSum8 = 0

@[simp] theorem ScheduleNeutralityCert.verified_any (c : ScheduleNeutralityCert) :
  ScheduleNeutralityCert.verified c := by
  intro P s H
  simpa using IndisputableMonolith.LNAL.schedule_neutrality_rotation (P:=P) (s:=s) H

def ScheduleNeutralityCert.fromSource (src : String) : ScheduleNeutralityCert :=
  let parsed := parseProgramFull src
  let emptyPhi : PhiIR.PhiAnalysis := { literals := #[], errors := #[], duplicateNames := [] }
  let emptyPackets : PhiIR.PacketAnalysis := {}
  let code := match parsed with
    | .ok out => out.code
    | .error _ => #[]
  let phi := match parsed with
    | .ok out => out.phi
    | .error _ => emptyPhi
  let packets := match parsed with
    | .ok out => out.packets
    | .error _ => emptyPackets
  let rep := staticChecks code phi packets
  { ok := rep.ok, errors := rep.errors }

/-- Cost ceiling certificate (|net GIVE−REGIVE| ≤ 4 per 8‑tick window). -/
structure CostCeilingCert where
  ok     : Bool
  errors : List String := []
deriving Repr

@[simp] def CostCeilingCert.verified (_c : CostCeilingCert) : Prop :=
  -- At 8k boundaries, window cost is bounded (indeed zero)
  (∀ (P : IndisputableMonolith.LNAL.LProgram)
     (s : IndisputableMonolith.LNAL.LState),
      IndisputableMonolith.LNAL.EightTickInvariant P s →
      ∀ k, Int.abs (IndisputableMonolith.LNAL.windowCostAt P s (8 * k)) ≤ 4)
  ∧
  -- There exists r ≤ 7 such that rotated boundaries are also bounded
  (∀ (P : IndisputableMonolith.LNAL.LProgram)
     (s : IndisputableMonolith.LNAL.LState),
      IndisputableMonolith.LNAL.EightTickInvariant P s →
      ∃ r, r ≤ 7 ∧ ∀ k,
        Int.abs (IndisputableMonolith.LNAL.windowCostAt P s (r + 8 * k)) ≤ 4)

@[simp] theorem CostCeilingCert.verified_any (c : CostCeilingCert) :
  CostCeilingCert.verified c := by
  constructor
  · intro P s H k; simpa using
      (IndisputableMonolith.LNAL.cost_ceiling_window_boundaries (P:=P) (s:=s) H k)
  · intro P s H; simpa using
      (IndisputableMonolith.LNAL.cost_ceiling_window_rotated (P:=P) (s:=s) H)

def CostCeilingCert.fromSource (src : String) : CostCeilingCert :=
  let parsed := parseProgramFull src
  let emptyPhi : PhiIR.PhiAnalysis := { literals := #[], errors := #[], duplicateNames := [] }
  let emptyPackets : PhiIR.PacketAnalysis := {}
  let code := match parsed with
    | .ok out => out.code
    | .error _ => #[]
  let phi := match parsed with
    | .ok out => out.phi
    | .error _ => emptyPhi
  let packets := match parsed with
    | .ok out => out.packets
    | .error _ => emptyPackets
  let rep := staticChecks code phi packets
  { ok := rep.ok, errors := rep.errors }

/-- SU(3) braid mask certificate: SU3Invariant preserved under lStep. -/
structure SU3MaskCert where deriving Repr

@[simp] def SU3MaskCert.verified (_c : SU3MaskCert) : Prop :=
  ∀ (P : IndisputableMonolith.LNAL.LProgram)
    (s : IndisputableMonolith.LNAL.LState),
    IndisputableMonolith.LNAL.SU3Invariant s →
    IndisputableMonolith.LNAL.SU3Invariant (IndisputableMonolith.LNAL.lStep P s)

@[simp] theorem SU3MaskCert.verified_any (c : SU3MaskCert) :
  SU3MaskCert.verified c := by
  intro P s h
  simpa using IndisputableMonolith.LNAL.lStep_preserves_su3 (P:=P) (s:=s) h

def SU3MaskCert.fromSource (_src : String) : SU3MaskCert :=
  {}

/-- J‑monotone per‑window budget certificate. -/
def JMonotoneCert := IndisputableMonolith.Certificates.JMonotoneCert

@[simp] def JMonotoneCert.verified :=
  IndisputableMonolith.Certificates.JMonotoneCert.verified

def JMonotoneCert.fromSource (src : String) : JMonotoneCert :=
  IndisputableMonolith.Certificates.JMonotoneCert.fromSource src

/-- Placeholder Units/K‑gate audit in bundle. -/
def UnitsKGateCert := IndisputableMonolith.Certificates.UnitsKGateCert

@[simp] def UnitsKGateCert.verified :=
  IndisputableMonolith.Certificates.UnitsKGateCert.verified

def UnitsKGateCert.fromSource (src : String) : UnitsKGateCert :=
  IndisputableMonolith.Certificates.UnitsKGateCert.fromSource src

end URCGenerators
end IndisputableMonolith
