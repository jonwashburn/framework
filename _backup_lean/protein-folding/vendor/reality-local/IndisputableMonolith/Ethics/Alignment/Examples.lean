import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Alignment
namespace Examples

open Classical

def Sphase : SigmaModel :=
  { stakeOf := fun p => some (if p.phase.val % 2 = 0 then "E" else "O") }

def p0 (δ : Int) : Posting := { delta := δ, phase := (0 : Fin 8), accurate := true }
def p1 (δ : Int) : Posting := { delta := δ, phase := (1 : Fin 8), accurate := true }

def m2 : Microcycle := { start := mkAlpha 0, steps := [p0 1, p0 (-1)] }

@[simp] theorem reciprocity_example :
  ReciprocitySigma0With m2 Sphase = true := by
  simp [ReciprocitySigma0With, sigmaBalances, bumpSigma, m2, p0, Sphase, List.foldl]

@[simp] theorem publish_invariant_id (m : Microcycle) :
  let idφ : Morph :=
    { onPosting := id
    , preserves_delta := by intro p; rfl
    , preserves_accuracy := by intro p; rfl
    , preserves_phase := by intro p; rfl }
  PublishP (mapMicro m idφ) ↔ PublishP m := by
  intro idφ; simpa using publish_invariant m idφ

end Examples
end Alignment
end Ethics
end IndisputableMonolith
