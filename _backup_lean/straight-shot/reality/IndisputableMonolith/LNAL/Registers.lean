import Mathlib

namespace IndisputableMonolith
namespace LNAL

/-!
Register block for LNAL execution state.

Matches the Reg6/Aux5 schema described in LNAL-Register-Mapping.tex.

All integer fields are intended to be kept within signed 32-bit ranges
by compile-time/static checks and clamping helpers in the VM.
-/

/-! ## Base bounds and register blocks -/

/-- Signed 32-bit bound used for simple clamping. -/
@[simp] def i32Bound : Int := 2147483648  -- 2^31

structure Reg6 where
  /-- ν_φ: log-frequency index (φ-lattice) -/
  nuPhi : Int
  /-- ℓ: curvature / orbital index -/
  ell   : Int
  /-- σ: parity bit encoded as {−1,0,+1} or small integers -/
  sigma : Int
  /-- τ: time-bin index within higher-level domain -/
  tau   : Int
  /-- k_⊥: transverse/mode index -/
  kPerp : Int
  /-- φ_e: entanglement phase (boolean) -/
  phiE  : Bool
deriving Repr, DecidableEq

structure Aux5 where
  /-- Rolling signed neighbor sum (domain-defined) -/
  neighborSum : Int
  /-- Active token count (0/1 expected by invariants) -/
  tokenCt     : Int
  /-- Hydration/free-volume proxy (domain-defined) -/
  hydrationS  : Int
  /-- Phase-locked indicator (core/glassy) -/
  phaseLock   : Bool
  /-- Reserved domain-specific slot -/
  freeSlot    : Int
deriving Repr, DecidableEq

namespace Reg6

@[simp] def zero : Reg6 :=
  { nuPhi := 0, ell := 0, sigma := 0, tau := 0, kPerp := 0, phiE := false }

end Reg6

namespace Aux5

@[simp] def zero : Aux5 :=
  { neighborSum := 0, tokenCt := 0, hydrationS := 0, phaseLock := false, freeSlot := 0 }

end Aux5

/-! ## Derived range predicates and invariants -/

/-- Closed form predicate for i32-style range: −2^31 < x < 2^31. -/
def I32Range (x : Int) : Prop := (-i32Bound < x) ∧ (x < i32Bound)

/-- Convert Bool to 0/1. -/
@[simp] def bit (b : Bool) : Int := if b then 1 else 0

/-- Parity in Z₂ represented as Int in {0,1}. -/
@[simp] def parity2 (z : Int) : Int := z % 2

/-- All integer fields of `Reg6` lie in i32-style bounds. -/
def Reg6.inI32 (r : Reg6) : Prop :=
  I32Range r.nuPhi ∧ I32Range r.ell ∧ I32Range r.sigma ∧ I32Range r.tau ∧ I32Range r.kPerp

/-- All integer fields of `Aux5` lie in i32-style bounds. -/
def Aux5.inI32 (a : Aux5) : Prop :=
  I32Range a.neighborSum ∧ I32Range a.tokenCt ∧ I32Range a.hydrationS ∧ I32Range a.freeSlot

/-- Parity coupling: (sigma + phiE) mod 2 equals phaseLock. -/
def parityInvariant (r : Reg6) (a : Aux5) : Prop :=
  ((parity2 r.sigma + bit r.phiE) % 2) = bit a.phaseLock

/-- Combined well-formedness for a register + auxiliary pair. -/
def WellFormed (r : Reg6) (a : Aux5) : Prop := r.inI32 ∧ a.inI32 ∧ parityInvariant r a

end LNAL
end IndisputableMonolith
