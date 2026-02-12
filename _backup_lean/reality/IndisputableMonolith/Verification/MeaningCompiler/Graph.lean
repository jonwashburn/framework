import Mathlib
import IndisputableMonolith.Verification.MeaningCompiler.Spec
import IndisputableMonolith.Token.WTokenId
import IndisputableMonolith.Water.WTokenIso

/-!
# Meaning Landscape Primitives: Graph & Metric

This module defines the **MeaningGraph** and associated metric structures
for navigating the semantic landscape. These primitives enable:

1. **Semantic nearness**: Define when two meanings are "close"
2. **Composition**: How meanings combine
3. **Navigation**: Path-finding through meaning space

## Key Principle

All definitions here are **intrinsic** (based on structural properties),
not **extrinsic** (based on English labels). String labels are UI-only
and NOT part of the formal structure.

-/

namespace IndisputableMonolith
namespace Verification
namespace MeaningCompiler

open Token Water
open scoped BigOperators

/-! ## MeaningSignature Extensions -/

/-- Operator response classification.
    Describes how a token responds to LNAL operators. -/
structure OperatorResponse where
  /-- LOCK response: does this token create a barrier? -/
  lockBarrier : Bool
  /-- BALANCE response: how strongly does it neutralize? -/
  balanceStrength : Fin 4  -- 0 = none, 3 = maximum
  /-- FOLD response: does it reduce dimension? -/
  foldReduces : Bool
  /-- BRAID compatibility: which triads can it participate in? -/
  braidCompatible : List (Fin 3 → ℕ)
  deriving DecidableEq, Repr

/-- Extended MeaningSignature with operator responses. -/
structure ExtendedSignature extends MeaningSignature where
  /-- Operator response profile -/
  operatorResponse : OperatorResponse
  /-- Gauge class index (0-3 for 4 basis classes) -/
  gaugeClass : Fin 4
  deriving Repr

/-- Compute gauge class from mode family.
    Same mode family → same gauge class. -/
def gaugeClassOf (mode : WTokenMode) : Fin 4 :=
  match mode with
  | .mode1_7 => 0
  | .mode2_6 => 1
  | .mode3_5 => 2
  | .mode4   => 3

/-- Default operator response for a given mode. -/
def defaultOperatorResponse (mode : WTokenMode) : OperatorResponse :=
  { lockBarrier := true  -- All tokens can lock
  , balanceStrength := 2  -- Medium neutralization
  , foldReduces := mode ≠ WTokenMode.mode4  -- Mode-4 is self-conjugate
  , braidCompatible := []  -- To be computed
  }

/-- Extend a basic signature to full signature. -/
def MeaningSignature.extend (sig : MeaningSignature) : ExtendedSignature :=
  { sig with
    operatorResponse := defaultOperatorResponse sig.modeFamily
    gaugeClass := gaugeClassOf sig.modeFamily
  }

/-! ## MeaningGraph Definition -/

/-- Edge type in the meaning graph.
    Represents a relationship between two tokens. -/
inductive EdgeType
  | transform    -- One can be transformed into the other (LNAL operation)
  | compose      -- They can be combined (BRAID compatible)
  | adjacent     -- Structurally adjacent (differ by one parameter)
  | orthogonal   -- Different basis classes (overlap = 0)
  deriving DecidableEq, Repr

/-- A weighted edge in the meaning graph. -/
structure MeaningEdge where
  source : WTokenId
  target : WTokenId
  edgeType : EdgeType
  /-- Weight (cost/distance) of the edge -/
  weight : ℝ

/-- The meaning graph: nodes are WTokens, edges are relationships. -/
structure MeaningGraph where
  /-- All 20 token nodes -/
  nodes : List WTokenId
  /-- Edges between tokens -/
  edges : List MeaningEdge
  /-- Node completeness: all 20 tokens present -/
  complete : nodes.length = 20

/-! ## Graph Construction -/

/-- Check if two tokens are in the same basis class. -/
def sameBasisClass (w1 w2 : WTokenId) : Bool :=
  gaugeClassOf (WTokenId.toSpec w1).mode = gaugeClassOf (WTokenId.toSpec w2).mode

/-- sameBasisClass is symmetric. -/
theorem sameBasisClass_symm (w1 w2 : WTokenId) :
    sameBasisClass w1 w2 = sameBasisClass w2 w1 := by
  simp [sameBasisClass, eq_comm]

/-- Check if two tokens are adjacent (differ by one parameter). -/
def areAdjacent (w1 w2 : WTokenId) : Bool :=
  let s1 := WTokenId.toSpec w1
  let s2 := WTokenId.toSpec w2
  -- Adjacent if they share mode and differ in either φ-level or τ-offset
  if s1.mode = s2.mode then
    (s1.phi_level ≠ s2.phi_level && s1.tau_offset = s2.tau_offset) ||
    (s1.phi_level = s2.phi_level && s1.tau_offset ≠ s2.tau_offset)
  else
    false

/-- areAdjacent is symmetric. -/
theorem areAdjacent_symm (w1 w2 : WTokenId) :
    areAdjacent w1 w2 = areAdjacent w2 w1 := by
  unfold areAdjacent
  -- All components are symmetric:
  -- - mode equality: s1.mode = s2.mode ↔ s2.mode = s1.mode
  -- - phi_level comparisons: symmetric
  -- - tau_offset comparisons: symmetric
  -- - Boolean OR is symmetric
  simp only [eq_comm, ne_comm, Bool.or_comm]

/-- Compute edge type between two tokens. -/
def computeEdgeType (w1 w2 : WTokenId) : EdgeType :=
  if w1 = w2 then .transform  -- Self-loop (identity transform)
  else if sameBasisClass w1 w2 then
    if areAdjacent w1 w2 then .adjacent
    else .compose
  else .orthogonal

/-- computeEdgeType is symmetric. -/
theorem computeEdgeType_symm (w1 w2 : WTokenId) :
    computeEdgeType w1 w2 = computeEdgeType w2 w1 := by
  simp only [computeEdgeType]
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, Ne.symm h, ↓reduceIte]
    rw [sameBasisClass_symm, areAdjacent_symm]

/-- Edge weight based on relationship type.
    Weights are chosen to reflect "semantic distance". -/
def edgeWeight (et : EdgeType) : ℝ :=
  match et with
  | .transform => 0.0    -- Same token
  | .adjacent => 0.5     -- One step in parameter space
  | .compose => 1.0      -- Same basis class, not adjacent
  | .orthogonal => 2.0   -- Different basis classes

/-- All 20 token IDs. -/
def allTokenNodes : List WTokenId :=
  [WTokenId.W0_Origin, WTokenId.W1_Emergence, WTokenId.W2_Polarity, WTokenId.W3_Harmony,
   WTokenId.W4_Power, WTokenId.W5_Birth, WTokenId.W6_Structure, WTokenId.W7_Resonance,
   WTokenId.W8_Infinity, WTokenId.W9_Truth, WTokenId.W10_Completion, WTokenId.W11_Inspire,
   WTokenId.W12_Transform, WTokenId.W13_End, WTokenId.W14_Connection, WTokenId.W15_Wisdom,
   WTokenId.W16_Illusion, WTokenId.W17_Chaos, WTokenId.W18_Twist, WTokenId.W19_Time]

/-- Build all edges for the meaning graph. -/
def buildEdges : List MeaningEdge :=
  allTokenNodes.flatMap fun w1 =>
    allTokenNodes.filterMap fun w2 =>
      if w1 = w2 then none  -- Skip self-loops
      else
        let et := computeEdgeType w1 w2
        some { source := w1, target := w2, edgeType := et, weight := edgeWeight et }

/-- Construct the canonical meaning graph. -/
def canonicalMeaningGraph : MeaningGraph :=
  { nodes := allTokenNodes
  , edges := buildEdges
  , complete := by native_decide
  }

/-! ## Semantic Distance Metric -/

/-- Semantic distance between two tokens.
    This is the minimum edge weight path (Dijkstra-like). -/
noncomputable def semanticDistance (w1 w2 : WTokenId) : ℝ :=
  if w1 = w2 then 0
  else
    let et := computeEdgeType w1 w2
    edgeWeight et

/-- Semantic distance is a pseudometric. -/
theorem semanticDistance_self (w : WTokenId) : semanticDistance w w = 0 := by
  simp [semanticDistance]

theorem semanticDistance_symm (w1 w2 : WTokenId) :
    semanticDistance w1 w2 = semanticDistance w2 w1 := by
  unfold semanticDistance
  by_cases h : w1 = w2
  · simp [h]
  · simp only [h, Ne.symm h, ↓reduceIte]
    rw [computeEdgeType_symm]

theorem semanticDistance_nonneg (w1 w2 : WTokenId) :
    0 ≤ semanticDistance w1 w2 := by
  unfold semanticDistance
  split
  · linarith
  · unfold edgeWeight
    cases computeEdgeType w1 w2 <;> norm_num

/-! ## Semantic Composition -/

/-- Result of composing two meanings. -/
inductive ComposeResult
  | success (combined : MeaningSignature)
  | incompatible (reason : String)
  deriving Repr

/-- Compose two tokens if they are BRAID-compatible.
    Tokens in the same basis class can be composed via BRAID. -/
def composeMeanings (w1 w2 : WTokenId) : ComposeResult :=
  let s1 := WTokenId.toSpec w1
  let s2 := WTokenId.toSpec w2
  if gaugeClassOf s1.mode = gaugeClassOf s2.mode then
    -- Same basis class: compose to higher φ-level (or wrap)
    let newPhiLevel :=
      match s1.phi_level, s2.phi_level with
      | .level0, p => p
      | p, .level0 => p
      | .level1, .level1 => PhiLevel.level2
      | .level1, .level2 => PhiLevel.level3
      | .level2, .level1 => PhiLevel.level3
      | .level2, .level2 => PhiLevel.level3
      | _, _ => PhiLevel.level3  -- Cap at level3
    .success { modeFamily := s1.mode, phiLevel := newPhiLevel, tauVariant := s1.tau_offset }
  else
    .incompatible "Different basis classes are orthogonal"

/-! ## Graph Export (Quarantined) -/

/-- JSON representation of an edge (for visualization). -/
structure EdgeJSON where
  source : String
  target : String
  edgeType : String
  weight : Float
  deriving Repr

/-- Convert weight ℝ to Float (approximate, for visualization only). -/
noncomputable def realToFloat (r : ℝ) : Float :=
  -- Approximate conversion - this is for visualization only
  if r ≤ 0 then 0.0
  else if r ≤ 0.5 then 0.5
  else if r ≤ 1.0 then 1.0
  else 2.0

/-- Local toString for WTokenId (without English labels). -/
def WTokenId.toStringSimple : WTokenId → String
  | .W0_Origin => "W0" | .W1_Emergence => "W1" | .W2_Polarity => "W2" | .W3_Harmony => "W3"
  | .W4_Power => "W4" | .W5_Birth => "W5" | .W6_Structure => "W6" | .W7_Resonance => "W7"
  | .W8_Infinity => "W8" | .W9_Truth => "W9" | .W10_Completion => "W10" | .W11_Inspire => "W11"
  | .W12_Transform => "W12" | .W13_End => "W13" | .W14_Connection => "W14" | .W15_Wisdom => "W15"
  | .W16_Illusion => "W16" | .W17_Chaos => "W17" | .W18_Twist => "W18" | .W19_Time => "W19"

/-- Local toString for EdgeType. -/
def EdgeType.toStringSimple : EdgeType → String
  | .transform => "transform"
  | .compose => "compose"
  | .adjacent => "adjacent"
  | .orthogonal => "orthogonal"

/-- Convert edge to JSON-like structure.
    Note: This is for visualization/export only, not certified surface. -/
noncomputable def MeaningEdge.toJSON (e : MeaningEdge) : EdgeJSON :=
  { source := WTokenId.toStringSimple e.source
  , target := WTokenId.toStringSimple e.target
  , edgeType := EdgeType.toStringSimple e.edgeType
  , weight := realToFloat e.weight
  }

/-- English labels for tokens (UI only, NOT certified surface). -/
def tokenLabel : WTokenId → String
  | .W0_Origin => "Origin"
  | .W1_Emergence => "Emergence"
  | .W2_Polarity => "Polarity"
  | .W3_Harmony => "Harmony"
  | .W4_Power => "Power"
  | .W5_Birth => "Birth"
  | .W6_Structure => "Structure"
  | .W7_Resonance => "Resonance"
  | .W8_Infinity => "Infinity"
  | .W9_Truth => "Truth"
  | .W10_Completion => "Completion"
  | .W11_Inspire => "Inspire"
  | .W12_Transform => "Transform"
  | .W13_End => "End"
  | .W14_Connection => "Connection"
  | .W15_Wisdom => "Wisdom"
  | .W16_Illusion => "Illusion"
  | .W17_Chaos => "Chaos"
  | .W18_Twist => "Twist"
  | .W19_Time => "Time"

/-! ## Summary -/

/-- Graph statistics for verification. -/
def graphStats (g : MeaningGraph) : String :=
  s!"Nodes: {g.nodes.length}, Edges: {g.edges.length}"

#eval graphStats canonicalMeaningGraph

end MeaningCompiler
end Verification
end IndisputableMonolith
