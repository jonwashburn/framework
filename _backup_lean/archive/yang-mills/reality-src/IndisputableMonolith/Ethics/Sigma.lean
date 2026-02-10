import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith

/-- Sigma-audit model provides a stakeholder mapping for postings. -/
structure SigmaModel where
  stakeOf : Posting → Option Stakeholder

/-- Update a (stake, sum) table with a delta. -/
def bumpSigma (tbl : List (Stakeholder × Int)) (s : Stakeholder) (δ : Int) : List (Stakeholder × Int) :=
  let rec go (acc : List (Stakeholder × Int)) (rest : List (Stakeholder × Int)) : List (Stakeholder × Int) :=
    match rest with
    | [] => (s, δ) :: acc |>.reverse
    | (t, v) :: rt =>
        if t = s then (acc.reverse ++ [(t, v + δ)] ++ rt) else go ((t, v) :: acc) rt
  go [] tbl

/-- Compute per-stakeholder sigma balances (sum of deltas) for the microcycle. -/
def sigmaBalances (m : Microcycle) (S : SigmaModel) : List (Stakeholder × Int) :=
  m.steps.foldl (fun acc p =>
    match S.stakeOf p with
    | none => acc
    | some s => bumpSigma acc s p.delta) []

/-- Reciprocity holds when all stakeholder balances are zero (Bool). -/
def ReciprocitySigma0With (m : Microcycle) (S : SigmaModel) : Bool :=
  (sigmaBalances m S).all (fun kv => kv.snd = 0)

/-- Prop counterpart. -/
def ReciprocitySigma0WP (m : Microcycle) (S : SigmaModel) : Prop :=
  ∀ s v, (s, v) ∈ sigmaBalances m S → v = 0

end IndisputableMonolith

