import Mathlib

namespace IndisputableMonolith
namespace LNAL

/-- 6-register machine. -/
abbrev Reg := Fin 6

inductive OpKind
| NOP | INC | DEC | MOV | ADD | SUB | XOR | AND | OR | NOT | LOAD | STORE | SWAP | JMP | JZ | HALT
deriving DecidableEq, Repr

structure Instr where
  kind : OpKind
  dst  : Option Reg := none
  src  : Option Reg := none
  imm  : Option Int := none
deriving Repr

/-- Program: instruction at address. -/
abbrev Program := Nat → Instr

structure State where
  reg    : Reg → Int
  ip     : Nat
  breath : Nat
  halted : Bool

namespace State

@[simp] def init : State := { reg := fun _ => 0, ip := 0, breath := 0, halted := false }
@[simp] def get (s : State) (r : Reg) : Int := s.reg r
@[simp] def set (s : State) (r : Reg) (v : Int) : State := { s with reg := fun q => if q = r then v else s.reg q }
@[simp] lemma get_set_same (s : State) (r : Reg) (v : Int) : (s.set r v).get r = v := by dsimp [get, set]; simp
@[simp] lemma get_set_other (s : State) (r q : Reg) (v : Int) (h : q ≠ r) : (s.set r v).get q = s.get q := by dsimp [get, set]; simp [h]

end State

@[simp] def breathPeriod : Nat := 1024
@[simp] def fetch (P : Program) (ip : Nat) : Instr := P ip
@[simp] def nextIP (s : State) : Nat := s.ip + 1
@[simp] def bumpBreath (s : State) : Nat := (s.breath + 1) % breathPeriod

def step (P : Program) (s : State) : State :=
  if s.halted then s else
  let i := fetch P s.ip
  let s' :=
    match i.kind with
    | OpKind.NOP   => s
    | OpKind.HALT  => { s with halted := true }
    | OpKind.INC   => match i.dst with | some r => s.set r (s.get r + 1) | none => s
    | OpKind.DEC   => match i.dst with | some r => s.set r (s.get r - 1) | none => s
    | OpKind.MOV   => match i.dst, i.src with | some rd, some rs => s.set rd (s.get rs) | _, _ => s
    | OpKind.ADD   => match i.dst, i.src with | some rd, some rs => s.set rd (s.get rd + s.get rs) | _, _ => s
    | OpKind.SUB   => match i.dst, i.src with | some rd, some rs => s.set rd (s.get rd - s.get rs) | _, _ => s
    | OpKind.XOR   => s
    | OpKind.AND   => s
    | OpKind.OR    => s
    | OpKind.NOT   => s
    | OpKind.LOAD  => s
    | OpKind.STORE => s
    | OpKind.SWAP  => match i.dst, i.src with | some rd, some rs => let v := s.get rd; (s.set rd (s.get rs)).set rs v | _, _ => s
    | OpKind.JMP   => match i.imm with | some off => { s with ip := s.ip + Nat.ofInt off.natAbs } | none => s
    | OpKind.JZ    => match i.dst, i.imm with | some rd, some off => if s.get rd = 0 then { s with ip := s.ip + Nat.ofInt off.natAbs } else s | _, _ => s
  let s'' := if s'.ip = s.ip then { s' with ip := nextIP s' } else s'
  { s'' with breath := bumpBreath s'', halted := s''.halted }

@[simp] lemma step_self (P : Program) (s : State) : step P s = step P s := rfl

lemma breath_lt_period (P : Program) (s : State) : (step P s).breath < breathPeriod := by
  dsimp [step, bumpBreath, breathPeriod]
  split <;> simp [Nat.mod_lt]

end LNAL
end IndisputableMonolith
