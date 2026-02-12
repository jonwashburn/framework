import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Decision

structure ParityCfg where
  groupOf : Request Unit → String
  tol : ℝ := 0.0

def acceptRate (P : Policy Unit) (cfg : ParityCfg) (xs : List (Request Unit)) (g : String) : ℝ :=
  let gs := xs.filter (fun r => cfg.groupOf r = g)
  if gs.length = 0 then 1 else
    let acc := (gs.filter (fun r => gatesOk (P:=P) r)).length
    (acc : ℝ) / (gs.length : ℝ)

def parityOk (P : Policy Unit) (cfg : ParityCfg) (xs : List (Request Unit)) : Bool :=
  let groups := (xs.map cfg.groupOf).eraseDups
  match groups with
  | [] => True
  | g :: gs =>
      let base := acceptRate P cfg xs g
      gs.all (fun h => |acceptRate P cfg xs h - base| ≤ cfg.tol)

@[simp] theorem parity_trivial (P : Policy Unit) (cfg : ParityCfg) :
  parityOk P cfg [] = true := by simp [parityOk]

end Decision
end Ethics
end IndisputableMonolith

