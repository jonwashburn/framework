import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Decision

def EqOppOKP (P : Policy A) (xs : List (Request A)) : Prop :=
  ∀ r ∈ xs, FairnessOKP r
def CalibOKP (P : Policy A) (xs : List (Request A)) : Prop :=
  ∀ r ∈ xs, ReciprocityOKP r
def IndivFairOKP (P : Policy A) (xs : List (Request A)) : Prop :=
  ∀ r ∈ xs, TemperanceOKP r
def CrossAgentOKP (P : Policy A) (xs : List (Request A)) : Prop :=
  ∀ r ∈ xs, WithinWindowP r ∧ UniqueInWindowP r

@[simp] lemma eqOppOk_true_iff (P : Policy A) (xs : List (Request A)) :
  eqOppOk (P:=P) xs = true ↔ EqOppOKP (P:=P) xs := by simp [eqOppOk, EqOppOKP]

@[simp] lemma calibOk_true_iff (P : Policy A) (xs : List (Request A)) :
  calibOk (P:=P) xs = true ↔ CalibOKP (P:=P) xs := by simp [calibOk, CalibOKP]

@[simp] lemma individualFairnessOk_true_iff (P : Policy A) (xs : List (Request A)) :
  individualFairnessOk (P:=P) xs = true ↔ IndivFairOKP (P:=P) xs := by simp [individualFairnessOk, IndivFairOKP]

@[simp] lemma crossAgentParityOk_true_iff (P : Policy A) (xs : List (Request A)) :
  crossAgentParityOk (P:=P) xs = true ↔ CrossAgentOKP (P:=P) xs := by simp [crossAgentParityOk, CrossAgentOKP]

@[simp] lemma fairnessBatchOk_mapped (P : Policy A) (xs : List (Request A)) (φ : Alignment.Morph) :
  fairnessBatchOk (P:=P) (xs.map (fun r => mapReqMicro r φ)) = fairnessBatchOk (P:=P) xs := by
  classical
  unfold fairnessBatchOk eqOppOk calibOk individualFairnessOk crossAgentParityOk
  simp [filterByGates, gatesOk, mapReqMicro]

end Decision
end Ethics
end IndisputableMonolith

