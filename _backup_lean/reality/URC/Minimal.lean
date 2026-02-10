import Mathlib
import IndisputableMonolith.URCAdapters.UnitsIdentity
import IndisputableMonolith.URCAdapters.EightBeat

/-! Minimal URC thin interface for fast CI builds.
    This file is independent of the heavy monolith and re-exports proven hooks.
-/

namespace URCMinimal

def UnitsProp : Prop := IndisputableMonolith.URCAdapters.units_identity_prop
def EightBeatProp : Prop := IndisputableMonolith.URCAdapters.eightbeat_prop
  -- Thin aliases to keep CI smoke independent of heavy modules

structure LawfulBridge : Prop where
  units  : UnitsProp
  eight  : EightBeatProp

@[simp] def bridge : LawfulBridge :=
  ⟨ IndisputableMonolith.URCAdapters.units_identity_holds
  , IndisputableMonolith.URCAdapters.eightbeat_holds ⟩

@[simp] theorem lawfulBridge_holds : LawfulBridge := bridge

end URCMinimal
