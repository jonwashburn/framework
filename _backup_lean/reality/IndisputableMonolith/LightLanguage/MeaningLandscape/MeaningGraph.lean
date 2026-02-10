import Mathlib
import IndisputableMonolith.LightLanguage.MeaningLandscape.SemanticCoordinate
import IndisputableMonolith.Token.WTokenId

/-!
# Meaning Graph Structure

This module defines the **relational structure** between WTokens as a graph.

## Main Definitions

* `MeaningRelation` — Types of edges (conjugate, same-mode, same-phi, compatible, etc.)
* `MeaningEdge` — Weighted directed edge between tokens
* `MeaningGraph` — The complete graph structure

## Key Properties

The meaning graph captures:
- **Conjugate pairs**: DFT modes k and (8-k) that form complex conjugates
- **Mode families**: Tokens sharing the same frequency band
- **φ-level siblings**: Tokens at the same amplitude level

-/

namespace IndisputableMonolith
namespace LightLanguage
namespace MeaningLandscape

open Water Token

/-! ## Relation Types -/

/-- Types of relationships between WTokens in the meaning graph -/
inductive MeaningRelation : Type
  | conjugate       -- Mode k paired with mode (8-k)
  | sameModeFamily  -- Same DFT mode family, different φ-level
  | samePhiLevel    -- Same φ-amplitude level, different mode
  | sameTauOffset   -- Same τ-offset (both τ₀ or both τ₂)
  | compatible      -- Can co-exist in a neutral window
  | incompatible    -- Cannot co-exist (sum violates neutrality)
  | sameOperatorClass  -- Same primary LNAL operator affinity
deriving DecidableEq, Repr, Hashable

instance : Fintype MeaningRelation where
  elems := {.conjugate, .sameModeFamily, .samePhiLevel, .sameTauOffset,
            .compatible, .incompatible, .sameOperatorClass}
  complete := fun x => by cases x <;> simp

/-! ## Edges -/

/-- A weighted edge in the meaning graph -/
structure MeaningEdge where
  /-- Source token -/
  source : WTokenId
  /-- Target token -/
  target : WTokenId
  /-- Type of relationship -/
  relation : MeaningRelation
  /-- Edge weight as rational (for decidability) -/
  weight : ℚ := 1
deriving DecidableEq, Repr

/-! ## Graph Structure -/

/-- The meaning graph: nodes are WTokens, edges encode relationships -/
structure MeaningGraph where
  /-- Set of nodes (all WTokens) -/
  nodes : Finset WTokenId
  /-- List of edges -/
  edges : List MeaningEdge
  /-- All WTokens are included -/
  nodes_complete : nodes = Finset.univ

/-! ## Edge Predicates -/

/-- Check if two tokens are in the same mode family -/
def sameModeFamilyPred (w1 w2 : WTokenId) : Bool :=
  let s1 := idToCoordinate w1
  let s2 := idToCoordinate w2
  s1.modeFamily == s2.modeFamily

/-- Check if two tokens have the same φ-level -/
def samePhiLevelPred (w1 w2 : WTokenId) : Bool :=
  let s1 := idToCoordinate w1
  let s2 := idToCoordinate w2
  s1.phiLevel == s2.phiLevel

/-- Check if two tokens have the same τ-offset -/
def sameTauOffsetPred (w1 w2 : WTokenId) : Bool :=
  let s1 := idToCoordinate w1
  let s2 := idToCoordinate w2
  s1.tauOffset == s2.tauOffset

/-- Check if two tokens have the same operator class -/
def sameOperatorClassPred (w1 w2 : WTokenId) : Bool :=
  let s1 := idToCoordinate w1
  let s2 := idToCoordinate w2
  s1.operatorClass == s2.operatorClass

/-- Check if two tokens are in the same conjugate pair family -/
def sameConjugatePairPred (w1 w2 : WTokenId) : Bool :=
  let s1 := idToCoordinate w1
  let s2 := idToCoordinate w2
  s1.conjugatePair == s2.conjugatePair

/-! ## Edge Constructors (using explicit token list) -/

/-- All WTokenIds as a list (for edge generation) -/
def allTokensList : List WTokenId :=
  [.W0_Origin, .W1_Emergence, .W2_Polarity, .W3_Harmony,
   .W4_Power, .W5_Birth, .W6_Structure, .W7_Resonance,
   .W8_Infinity, .W9_Truth, .W10_Completion, .W11_Inspire,
   .W12_Transform, .W13_End, .W14_Connection, .W15_Wisdom,
   .W16_Illusion, .W17_Chaos, .W18_Twist, .W19_Time]

/-- Generate all same-mode-family edges -/
def modeFamilyEdges : List MeaningEdge :=
  allTokensList.flatMap fun w1 =>
    allTokensList.filterMap fun w2 =>
      if w1 ≠ w2 && sameModeFamilyPred w1 w2 then
        some { source := w1, target := w2, relation := .sameModeFamily, weight := 1 }
      else
        none

/-- Generate all same-φ-level edges -/
def phiLevelEdges : List MeaningEdge :=
  allTokensList.flatMap fun w1 =>
    allTokensList.filterMap fun w2 =>
      if w1 ≠ w2 && samePhiLevelPred w1 w2 then
        some { source := w1, target := w2, relation := .samePhiLevel, weight := 1 }
      else
        none

/-- Generate all same-τ-offset edges -/
def tauOffsetEdges : List MeaningEdge :=
  allTokensList.flatMap fun w1 =>
    allTokensList.filterMap fun w2 =>
      if w1 ≠ w2 && sameTauOffsetPred w1 w2 then
        some { source := w1, target := w2, relation := .sameTauOffset, weight := 1 }
      else
        none

/-- Generate all same-operator-class edges -/
def operatorClassEdges : List MeaningEdge :=
  allTokensList.flatMap fun w1 =>
    allTokensList.filterMap fun w2 =>
      if w1 ≠ w2 && sameOperatorClassPred w1 w2 then
        some { source := w1, target := w2, relation := .sameOperatorClass, weight := 1 }
      else
        none

/-- Generate conjugate pair edges (same conjugate pair family) -/
def conjugateEdges : List MeaningEdge :=
  allTokensList.flatMap fun w1 =>
    allTokensList.filterMap fun w2 =>
      if w1 ≠ w2 && sameConjugatePairPred w1 w2 then
        some { source := w1, target := w2, relation := .conjugate, weight := 1 }
      else
        none

/-! ## Canonical Graph -/

/-- The canonical meaning graph for the 20 WTokens -/
def canonicalMeaningGraph : MeaningGraph where
  nodes := Finset.univ
  edges := modeFamilyEdges ++ phiLevelEdges ++ tauOffsetEdges ++
           operatorClassEdges ++ conjugateEdges
  nodes_complete := rfl

/-! ## Graph Properties -/

/-- Number of nodes in the canonical graph -/
theorem canonicalGraph_node_count : canonicalMeaningGraph.nodes.card = 20 := by
  simp only [canonicalMeaningGraph]
  exact WTokenId.card_eq_20

/-- Get all edges of a specific relation type -/
def edgesOfType (g : MeaningGraph) (rel : MeaningRelation) : List MeaningEdge :=
  g.edges.filter fun e => e.relation == rel

/-- Get all neighbors of a token (ignoring relation type) -/
def neighbors (g : MeaningGraph) (w : WTokenId) : List WTokenId :=
  (g.edges.filter fun e => e.source == w).map fun e => e.target

/-- Get neighbors by specific relation -/
def neighborsByRelation (g : MeaningGraph) (w : WTokenId) (rel : MeaningRelation) : List WTokenId :=
  (g.edges.filter fun e => e.source == w && e.relation == rel).map fun e => e.target

/-- Degree of a node (number of outgoing edges) -/
def degree (g : MeaningGraph) (w : WTokenId) : ℕ :=
  (g.edges.filter fun e => e.source == w).length

/-! ## Export to Graphviz -/

/-- Convert a relation to a color for visualization -/
def relationToColor : MeaningRelation → String
  | .conjugate => "red"
  | .sameModeFamily => "blue"
  | .samePhiLevel => "green"
  | .sameTauOffset => "orange"
  | .compatible => "gray"
  | .incompatible => "black"
  | .sameOperatorClass => "purple"

/-- Convert graph to Graphviz DOT format -/
def toGraphvizDot (g : MeaningGraph) : String :=
  let header := "digraph MeaningGraph {\n  rankdir=LR;\n  node [shape=circle];\n\n"
  let nodeLines := allTokensList.map fun w =>
    let coord := idToCoordinate w
    s!"  \"{repr w}\" [label=\"{coord.displayLabel}\"];\n"
  let edgeLines := g.edges.map fun e =>
    let color := relationToColor e.relation
    s!"  \"{repr e.source}\" -> \"{repr e.target}\" [color={color}];\n"
  let footer := "}\n"
  header ++ String.join nodeLines ++ String.join edgeLines ++ footer

/-! ## Statistics -/

/-- Count edges by type -/
def edgeCountByType (g : MeaningGraph) : List (MeaningRelation × ℕ) :=
  [.conjugate, .sameModeFamily, .samePhiLevel, .sameTauOffset,
   .sameOperatorClass, .compatible, .incompatible].map fun rel =>
    (rel, (edgesOfType g rel).length)

/-- Total edge count -/
def totalEdgeCount (g : MeaningGraph) : ℕ := g.edges.length

/-- Mode family edge count: each of 4 families has 4-8 tokens,
    forming n(n-1) directed edges within family -/
theorem modeFamilyEdges_count : modeFamilyEdges.length = 92 := by native_decide

/-- Phi level edge count: 4 levels with 5 tokens each -/
theorem phiLevelEdges_count : phiLevelEdges.length = 80 := by native_decide

/-- Conjugate edge count: same as mode family (conjugate pairs overlap with mode families) -/
theorem conjugateEdges_count : conjugateEdges.length = 92 := by native_decide

/-! ## Summary -/

/-- Summary string for the meaning graph -/
def graphSummary (g : MeaningGraph) : String :=
  let modeCount := (edgesOfType g .sameModeFamily).length
  let phiCount := (edgesOfType g .samePhiLevel).length
  let tauCount := (edgesOfType g .sameTauOffset).length
  let opCount := (edgesOfType g .sameOperatorClass).length
  let conjCount := (edgesOfType g .conjugate).length
  s!"MeaningGraph: {g.nodes.card} nodes, {g.edges.length} edges\n" ++
  s!"  Mode family edges: {modeCount}\n" ++
  s!"  Phi level edges: {phiCount}\n" ++
  s!"  Tau offset edges: {tauCount}\n" ++
  s!"  Operator class edges: {opCount}\n" ++
  s!"  Conjugate edges: {conjCount}"

#eval graphSummary canonicalMeaningGraph

end MeaningLandscape
end LightLanguage
end IndisputableMonolith
