import IndisputableMonolith.OctaveKernel.Basic
import IndisputableMonolith.LNAL.VM

namespace IndisputableMonolith
namespace OctaveKernel
namespace Instances

open IndisputableMonolith
open IndisputableMonolith.LNAL

/-!
# OctaveKernel.Instances.LNALAligned

A conservative “meaning-layer” witness using the existing LNAL VM’s **breath clock**
projected mod 8 as the kernel phase.

This is *not* claiming that the LNAL VM is physics; it is just packaging an
already-existing 8-tick structure into the `OctaveKernel.Layer` interface.

Key design choice:
- We use `phase := breath % 8`. This gives an **unconditional** `StepAdvances`
  proof (no scheduler assumptions needed).

Costs/ledger in this witness are intentionally trivial (cost=0, admissible=True);
the point here is the **8-beat kernel clock** and its preservation under `lStep`.
-/

/-! ## Breath-mod-8 witness layer -/

/-- Kernel witness layer for LNAL using `breath % 8` as the phase. -/
def LNALBreathLayer (P : LProgram) : Layer :=
{ State := LState
, phase := fun s => ⟨s.breath % 8, Nat.mod_lt _ (by decide)⟩
, cost := fun _ => 0
, admissible := fun _ => True
, step := lStep P
}

private lemma lStep_breath_eq (P : LProgram) (s : LState) :
  (lStep P s).breath = (s.breath + 1) % breathPeriod := by
  -- Breath update is applied at the very end of `lStep`, regardless of opcode.
  -- We keep this proof local to avoid turning `LNAL/VM.lean` into a theorem file.
  unfold lStep
  by_cases hH : s.halted
  · simp [hH, lBumpBreath, breathPeriod]
  ·
    -- In the non-halted case, all opcode branches keep `breath := s.breath`.
    cases hop : (P s.ip).op <;> simp [hH, lFetch, hop, lBumpBreath, breathPeriod]

theorem LNALBreathLayer_stepAdvances (P : LProgram) :
  Layer.StepAdvances (LNALBreathLayer P) := by
  intro s
  -- Reduce equality in `Fin 8` to equality of underlying Nat values.
  ext
  simp [LNALBreathLayer, Fin.val_add, lStep_breath_eq, Nat.add_mod]

theorem LNALBreathLayer_preservesAdmissible (P : LProgram) :
  Layer.PreservesAdmissible (LNALBreathLayer P) := by
  intro _s hs
  trivial

theorem LNALBreathLayer_nonincreasingCost (P : LProgram) :
  Layer.NonincreasingCost (LNALBreathLayer P) := by
  intro _s hs
  simp [LNALBreathLayer]

end Instances
end OctaveKernel
end IndisputableMonolith
