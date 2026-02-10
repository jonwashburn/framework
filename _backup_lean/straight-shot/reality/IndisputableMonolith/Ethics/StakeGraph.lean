import Mathlib

namespace IndisputableMonolith
namespace Ethics

/-- Stakeholder label. -/
abbrev Stakeholder := String

/-- Stakeholder graph for COI detection. -/
structure StakeGraph where
  edge : Stakeholder → Stakeholder → Bool

namespace StakeGraph

def contains (xs : List Stakeholder) (s : Stakeholder) : Bool :=
  xs.any (fun x => decide (x = s))

def neighbors (G : StakeGraph) (nodes : List Stakeholder) (s : Stakeholder) : List Stakeholder :=
  nodes.filter (fun t => G.edge s t)

def reachable (G : StakeGraph) (nodes : List Stakeholder) (src dst : Stakeholder) : Bool :=
  let rec dfs (front : List Stakeholder) (visited : List Stakeholder) : Bool :=
    match front with
    | [] => False
    | v :: vs =>
        if decide (v = dst) then True else
        let nbrs := neighbors G nodes v
        let fresh := nbrs.filter (fun w => ¬ contains visited w)
        dfs (vs ++ fresh) (v :: visited)
  dfs [src] []

def mutualReachable (G : StakeGraph) (nodes : List Stakeholder) (s t : Stakeholder) : Bool :=
  reachable G nodes s t && reachable G nodes t s

def hasCycle (G : StakeGraph) (nodes : List Stakeholder) : Bool :=
  nodes.any (fun s => G.edge s s)
  || nodes.any (fun s =>
        nodes.any (fun t => (¬ decide (s = t)) && mutualReachable G nodes s t))

end StakeGraph
end Ethics
end IndisputableMonolith

