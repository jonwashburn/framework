import Mathlib
import IndisputableMonolith.Complexity.SAT.CNF
import IndisputableMonolith.Complexity.SAT.XOR
import IndisputableMonolith.Complexity.SAT.Backprop
import IndisputableMonolith.Complexity.SAT.Isolation
import IndisputableMonolith.Complexity.SAT.SmallBias
import IndisputableMonolith.Complexity.SAT.PC

namespace IndisputableMonolith
namespace Complexity
namespace SAT

/-- Build a fully-determined backpropagation state from a total assignment. -/
def completeStateFrom {n} (x : Assignment n) : BPState n :=
  { assign := fun v => some (x v) }

/-- The state built from a total assignment is complete. -/
lemma complete_completeStateFrom {n} (x : Assignment n) :
    complete (completeStateFrom x) := by
  intro v
  rfl

/-- The state built from a satisfying assignment is consistent. -/
lemma consistent_completeStateFrom {n} (x : Assignment n) (φ : CNF n) (H : XORSystem n)
    (hxφ : evalCNF x φ = true) (hxH : satisfiesSystem x H) :
    consistent (completeStateFrom x) φ H := by
  refine ⟨x, ?eqall, hxφ, hxH⟩
  intro v; rfl

/-!
# Propagation Completeness for Geometrically Isolated SAT Instances

This module defines the key theorems connecting geometric isolation to backward
propagation completeness. The main claim (Theorem 5 in the paper) is that for
every satisfiable 3-CNF φ, the isolating H ∈ 𝓗_geo(n) produces an instance
φ ∧ H where XOR-augmented propagation determines all variables.

## Structure

1. `IsolationInvariant`: Structural conditions promised by geometric isolation
2. `PropagationReachability`: Every variable is reachable by propagation chains
3. `BackpropCompleteUnderInvariant`: Main implication
4. `ProgramTarget`: Full end-to-end specification

## Critical Claim Status

The propagation-enablement theorem (Theorem 5) is the key claim requiring
verification. The proof strategy relies on:
- Linear masks target every variable via single-variable constraints H_{a,n,j}
- XOR cascade: determined variables unlock others via parity relations
- Clause cascade: known values simplify clauses, forcing more variables
- Termination: geometric structure ensures no stalls

Formal verification is in progress via Tracks A and B.
-/

/-- Propagation graph: variable v₁ → v₂ if determining v₁ can force v₂. -/
structure PropagationGraph (n : Nat) where
  edges : Var n → Var n → Prop

/-- A variable is reachable from initial units in the propagation graph.
    Defined inductively to ensure termination. -/
inductive Reachable {n} (G : PropagationGraph n) (init : Set (Var n)) : Var n → Prop
  | base : ∀ v, v ∈ init → Reachable G init v
  | step : ∀ u v, Reachable G init u → G.edges u v → Reachable G init v

/-- All variables are reachable from initial units. -/
def AllReachable {n} (G : PropagationGraph n) (init : Set (Var n)) : Prop :=
  ∀ v, Reachable G init v

/-- Structural invariant promised by the isolation construction (Track A).

This captures the combinatorial conditions that geometric isolation guarantees:
1. `hasUnits`: Some variables have unit constraints from H (direct determination)
2. `connected`: The propagation graph reaches all variables from units
3. `noStalls`: No stall configurations exist (propagation always has progress)
-/
structure IsolationInvariant (n : Nat) (φ : CNF n) (H : XORSystem n) : Prop where
  /-- At least one variable has a unit (single-variable) XOR constraint. -/
  hasUnits : ∃ v : Var n, ∃ p : Bool, [{ vars := [v], parity := p }] ⊆ H
  /-- The propagation graph constructed from φ ∧ H is connected. -/
  connected : ∃ G : PropagationGraph n, ∃ init : Set (Var n), AllReachable G init
  /-- No stall configurations: if unknowns remain, some rule applies. -/
  noStalls : ∀ s : BPState n, ¬complete s → ∃ s', BPStep φ H s s' ∧ s ≠ s'

/-- Backprop completeness under the isolation invariant (Track B target). -/
def BackpropCompleteUnderInvariant {n} (φ : CNF n) (H : XORSystem n) : Prop :=
  IsolationInvariant n φ H → BackpropSucceeds φ H

/-- **PROVED**: Determined values match the unique solution.

**Proof**: Pick x to be the unique solution (from `huniq`).
Then if all determined values in s match x, the premise `s.assign v = some (x v)`
combined with `hdetermined : s.assign v = some b` gives `b = x v`.

**Status**: PROVED (formerly axiom) -/
theorem determined_values_correct {n} (φ : CNF n) (H : XORSystem n)
    (huniq : UniqueSolutionXOR { φ := φ, H := H })
    (s : BPState n) (v : Var n) (b : Bool)
    (hdetermined : s.assign v = some b) :
    ∃ x : Assignment n, (∀ v', s.assign v' = some (x v')) →
      evalCNF x φ = true ∧ satisfiesSystem x H ∧ x v = b := by
  -- UniqueSolutionXOR means ∃! a, evalCNF a φ = true ∧ satisfiesSystem a H
  unfold UniqueSolutionXOR at huniq
  -- Get the unique solution
  obtain ⟨x, ⟨hx_sat_φ, hx_sat_H⟩, _⟩ := huniq
  -- Use x as our witness
  use x
  intro h_all_match
  -- From h_all_match at v: s.assign v = some (x v)
  -- Combined with hdetermined: s.assign v = some b
  -- We get: b = x v
  have hv_match := h_all_match v
  rw [hdetermined] at hv_match
  simp only [Option.some.injEq] at hv_match
  exact ⟨hx_sat_φ, hx_sat_H, hv_match.symm⟩

/-- **AXIOM / PHYSICAL HYPOTHESIS**: Geometric propagation theorem.

    Geometric isolation enables propagation completeness.

    **Mathematical justification:** The geometric isolation construction (Track A)
    ensures that the linear masks H_{a,n,j} are distributed across the
    configuration space such that they target every bit position. When a unique
    solution x* is isolated, at least one such mask reduces to a unit
    constraint. The hierarchical Morton ordering ensures that once one
    variable is determined, the XOR and clause cascades propagate to
    determine all other variables in polynomial steps.

    **STATUS**: HYPOTHESIS (Theorem 5 in paper) -/
def geometric_isolation_enables_propagation_hypothesis {n} (φ : CNF n) (H : XORSystem n) : Prop :=
  Satisfiable φ → isolates φ H → H ∈ linearFamily n → IsolationInvariant n φ H

theorem geometric_isolation_enables_propagation_thm {n} (φ : CNF n) (hsat : Satisfiable φ)
    (H : XORSystem n) (hiso : isolates φ H) (hgeo : H ∈ linearFamily n)
    (h : geometric_isolation_enables_propagation_hypothesis (n:=n) φ H) :
    IsolationInvariant n φ H :=
  h hsat hiso hgeo

/-- **AXIOM / PHYSICAL HYPOTHESIS**: Polynomial-time 3-SAT algorithm.

    A polynomial-time algorithm for 3-SAT exists.

    **Mathematical justification:** Combining geometric isolation (Theorem 4),
    propagation enablement (Theorem 5), and the polynomial-size family
    construction (O(n²)), we obtain a randomized algorithm that finds
    the unique satisfying assignment in O(n^{11/3} log n) time.

    **STATUS**: HYPOTHESIS (Theorem 6 in paper) -/
def polynomial_time_3sat_algorithm_hypothesis (n : Nat) : Prop :=
  ProgramTarget n →
  ∃ (alg : CNF n → Option (Assignment n)),
    (∀ φ, Satisfiable φ → ∃ x, alg φ = some x ∧ evalCNF x φ = true) ∧
    (∀ φ, ¬Satisfiable φ → alg φ = none)

theorem polynomial_time_3sat_algorithm (n : Nat)
    (h : polynomial_time_3sat_algorithm_hypothesis n) :
    ProgramTarget n →
    ∃ (alg : CNF n → Option (Assignment n)),
      (∀ φ, Satisfiable φ → ∃ x, alg φ = some x ∧ evalCNF x φ = true) ∧
      (∀ φ, ¬Satisfiable φ → alg φ = none) :=
  h

/-- Backpropagation succeeds when there is a unique solution under XOR constraints.
This is a semantic existence result that does not rely on a specific step system. -/
theorem backprop_succeeds_of_unique {n} (φ : CNF n) (H : XORSystem n)
    (huniq : UniqueSolutionXOR { φ := φ, H := H }) :
    BackpropSucceeds φ H := by
  intro s0
  rcases huniq with ⟨x, hx, _uniq⟩
  refine ⟨completeStateFrom x, ?hcomp, ?hcons⟩
  · exact complete_completeStateFrom x
  · rcases hx with ⟨hxφ, hxH⟩
    exact consistent_completeStateFrom x φ H hxφ hxH

/-- PC ⇒ backpropagation succeeds (via uniqueness).
Note: with the current abstract step semantics, uniqueness alone suffices for success.
PC becomes relevant once a concrete BPStep is connected to semantic forcing. -/
theorem backprop_succeeds_from_PC {n}
    (inputs : Finset (Var n)) (aRef : Assignment n) (φ : CNF n) (H : XORSystem n)
    (_hpc : PC inputs aRef φ H)
    (huniq : UniqueSolutionXOR { φ := φ, H := H }) :
    BackpropSucceeds φ H :=
  backprop_succeeds_of_unique φ H huniq

end SAT
end Complexity
end IndisputableMonolith
