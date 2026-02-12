import Mathlib
import IndisputableMonolith.Fusion.NuclearBridge
import IndisputableMonolith.Fusion.BindingEnergy

/-!
# Fusion Reaction Network

This module formalizes fusion reaction pathways as a weighted graph
where edge weights combine stability distance metrics.

## Key Properties

1. **Monotonicity**: Magic-favorable reactions decrease stability distance
2. **Attractors**: Doubly-magic nuclei have minimal stability distance
3. **α-ladder**: Standard nucleosynthesis pathway includes magic endpoints
-/

namespace IndisputableMonolith
namespace Fusion
namespace ReactionNetwork

open NuclearBridge

noncomputable section

/-! ## Reaction Graph Elements -/

/-- A node in the fusion network is a nuclear configuration. -/
abbrev Node := NuclearConfig

/-- An edge represents a fusion reaction: A + B → C. -/
structure Edge where
  reactantA : Node
  reactantB : Node
  product : Node
  conserves_Z : product.Z = reactantA.Z + reactantB.Z
  conserves_N : product.N = reactantA.N + reactantB.N

/-- Stability improvement for a reaction (positive = product more stable). -/
def stabilityImprovement (e : Edge) : ℤ :=
  (stabilityDistance e.reactantA + stabilityDistance e.reactantB : ℕ) -
  stabilityDistance e.product

/-- A reaction is magic-favorable if product is closer to magic numbers. -/
def isMagicFavorable (e : Edge) : Prop :=
  stabilityImprovement e ≥ 0

/-- Edge weight: lower = more favorable. -/
def edgeWeight (e : Edge) : ℝ :=
  (stabilityDistance e.product : ℝ)

/-! ## Network Structure -/

/-- A fusion network is a collection of edges. -/
structure FusionNetwork where
  edges : List Edge

/-- Edges leaving a given node. -/
def outgoingEdges (net : FusionNetwork) (n : Node) : List Edge :=
  net.edges.filter (fun e => e.reactantA = n ∨ e.reactantB = n)

/-! ## Attractor Properties -/

/-- Doubly-magic nuclei have zero stability distance. -/
theorem doublyMagic_zero_distance (cfg : Node)
    (h : Nuclear.MagicNumbers.isDoublyMagic cfg.Z cfg.N) :
    stabilityDistance cfg = 0 :=
  stabilityDistance_zero_of_doublyMagic cfg h

/-! ## α-Capture -/

/-- An α-capture edge has He-4 as a reactant. -/
def isAlphaCapture (e : Edge) : Prop :=
  e.reactantB = Helium4 ∨ e.reactantA = Helium4

/-- Standard α-capture edge from A. -/
def alphaEdge (A : Node) : Edge where
  reactantA := A
  reactantB := Helium4
  product := ⟨A.Z + 2, A.N + 2⟩
  conserves_Z := by simp only [Helium4]
  conserves_N := by simp only [Helium4]

/-- The α-capture network from C-12 to Ca-40. -/
def alphaNetwork : FusionNetwork where
  edges := [
    alphaEdge Carbon12,
    alphaEdge Oxygen16,
    alphaEdge ⟨10, 10⟩,
    alphaEdge ⟨12, 12⟩,
    alphaEdge ⟨14, 14⟩,
    alphaEdge ⟨16, 16⟩,
    alphaEdge Argon36,
    alphaEdge Calcium40
  ]

/-! ## Key Theorems -/

/-- Magic-favorable reactions decrease stability distance. -/
theorem magicFavorable_decreases_distance (e : Edge) (h : isMagicFavorable e) :
    stabilityDistance e.product ≤
      stabilityDistance e.reactantA + stabilityDistance e.reactantB := by
  unfold isMagicFavorable stabilityImprovement at h
  omega

/-- O-16 is doubly-magic (Z=8, N=8). -/
theorem o16_is_doublyMagic : Nuclear.MagicNumbers.isDoublyMagic 8 8 := by
  unfold Nuclear.MagicNumbers.isDoublyMagic Nuclear.MagicNumbers.isMagic
    Nuclear.MagicNumbers.magicNumbers
  decide

/-- Ca-40 is doubly-magic (Z=20, N=20). -/
theorem ca40_is_doublyMagic : Nuclear.MagicNumbers.isDoublyMagic 20 20 := by
  unfold Nuclear.MagicNumbers.isDoublyMagic Nuclear.MagicNumbers.isMagic
    Nuclear.MagicNumbers.magicNumbers
  decide

/-- O-16 has zero stability distance. -/
theorem o16_zero_distance : stabilityDistance Oxygen16 = 0 := o16_stability_zero

/-- Ca-40 has zero stability distance. -/
theorem ca40_zero_distance : stabilityDistance Calcium40 = 0 := ca40_stability_zero

/-- A doubly-magic nucleus has minimum stability distance (zero). -/
theorem doublyMagic_is_minimum (cfg : Node)
    (h : Nuclear.MagicNumbers.isDoublyMagic cfg.Z cfg.N) :
    ∀ other : Node, stabilityDistance cfg ≤ stabilityDistance other := by
  intro other
  rw [doublyMagic_zero_distance cfg h]
  exact Nat.zero_le _

/-- Weighted path length is the sum of product stability distances. -/
def pathWeight (edges : List Edge) : ℝ :=
  (edges.map edgeWeight).sum

/-- Path weight is non-negative. -/
theorem pathWeight_nonneg (edges : List Edge) : 0 ≤ pathWeight edges := by
  unfold pathWeight
  apply List.sum_nonneg
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨e, _, rfl⟩ := hw
  unfold edgeWeight
  exact Nat.cast_nonneg _

end

end ReactionNetwork
end Fusion
end IndisputableMonolith
