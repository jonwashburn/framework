import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Decision

def crossAgentParityOk (P : Policy A) (xs : List (Request A)) : Bool :=
  let ys := filterByGates (P:=P) xs
  match P.agentOf? with
  | none => True
  | some agentOf =>
      let agents := (ys.map agentOf).eraseDups
      match agents with
      | [] => True
      | a :: as =>
          let rate (a : String) : ℝ :=
            let zs := ys.filter (fun r => agentOf r = a)
            if zs.length = 0 then 1 else
              let acc := (zs.filter (fun r => gatesOk (P:=P) r)).length
              (acc : ℝ) / (zs.length : ℝ)
          let base := rate a
          as.all (fun b => |rate b - base| ≤ P.parityTol)

def fairnessBatchOk (P : Policy A) (xs : List (Request A)) : Bool :=
  eqOppOk (P:=P) xs && calibOk (P:=P) xs && individualFairnessOk (P:=P) xs && crossAgentParityOk (P:=P) xs

def chooseBestWithAllFairness (P : Policy A) (xs : List (Request A)) : Option (Request A) :=
  let ys := filterByGatesWithParity (P:=P) xs
  if fairnessBatchOk (P:=P) ys then
    match chooseBest (P:=P) ys with
    | some r => some r
    | none => chooseBest (P:=P) xs
  else
    chooseBest (P:=P) xs

def chooseTruthful (P : Policy A) (xs : List (Request A)) : Option (Request A) :=
  match P.evidence? with
  | none => chooseBestWithAllFairness (P:=P) xs
  | some E =>
      let ys := filterByGatesWithParity (P:=P) xs
      match ys with
      | [] => chooseBestWithAllFairness (P:=P) xs
      | y :: yt =>
          let best := yt.foldl (fun b n =>
            if Truth.divergenceCount E n.claims < Truth.divergenceCount E b.claims then n else b) y
          some best

end Decision
end Ethics
end IndisputableMonolith
