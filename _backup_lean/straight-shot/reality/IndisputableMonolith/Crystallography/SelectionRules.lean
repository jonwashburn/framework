import Mathlib

/-!
# Crystallography Selection Rules (scaffold)

LNAL-inspired selection: eight-window neutrality and legal SU(3) triads
translated into reciprocal-space motif constraints. This module provides simple
predicates and counters usable for empirical bias tests against space-group
frequencies.
-/

namespace IndisputableMonolith
namespace Crystallography
namespace SelectionRules

open scoped BigOperators

/‑ A reciprocal-space motif encoded as a triple of Miller-like integers. -/
structure Triad where
  h : ℤ
  k : ℤ
  l : ℤ
  deriving Repr, DecidableEq

/‑ Legal triad proxy: parity and sum constraints (scaffold). -/
def legalTriad (t : Triad) : Bool :=
  let s := t.h + t.k + t.l
  (s % 2 = 0) && (t.h ≠ 0 ∨ t.k ≠ 0 ∨ t.l ≠ 0)

/‑ Eight-window neutrality diagnostic over a sequence of motif weights. -/
def neutral8 (w : ℕ → ℝ) (i0 : ℕ) : ℝ :=
  (Finset.range 8).sum (fun i => w (i0 + i))

/‑ Count legal triads in a finite list. -/
def countLegal (ts : List Triad) : ℕ :=
  ts.countP (fun t => legalTriad t)

end SelectionRules
end Crystallography
end IndisputableMonolith
