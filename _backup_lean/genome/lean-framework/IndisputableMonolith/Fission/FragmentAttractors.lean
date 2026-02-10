import Mathlib
import IndisputableMonolith.Fusion.NuclearBridge

/-!
# Fission Fragment Attractors

This module begins the fission-side analogue of the fusion reaction network:
we model a fission event as a split edge `parent -> (fragA, fragB)`.

The core (proof-friendly) baseline is a discrete split cost functional based on
`stabilityDistance` (distance-to-magic). Under this cost, splits into magic/doubly-magic
fragments achieve provable minima.

This corresponds to Phase **FI1** in `planning/FUSION_FISSION_RESEARCH_EXECUTION_PLAN.md`.
-/

namespace IndisputableMonolith
namespace Fission
namespace FragmentAttractors

open Fusion.NuclearBridge

/-! ## Graph Elements -/

/-- A node is a nuclear configuration. -/
abbrev Node := NuclearConfig

/-- A fission split edge: parent -> (fragA, fragB) with conservation. -/
structure SplitEdge where
  parent : Node
  fragA : Node
  fragB : Node
  conserves_Z : parent.Z = fragA.Z + fragB.Z
  conserves_N : parent.N = fragA.N + fragB.N

/-! ## Split cost functional -/

/-- Split cost: sum of fragment stability distances. -/
def splitCost (e : SplitEdge) : ℕ :=
  stabilityDistance e.fragA + stabilityDistance e.fragB

/-! ## Penalty-augmented split cost (physics-layer hook)

The baseline `splitCost` is purely topological/discrete. To model fission yield
peaks we will add an explicit penalty term capturing (e.g.) Coulomb repulsion
and surface energy, and prove minimizer statements under explicit hypotheses.
-/

/-- Total split cost: (cast) base cost + user-supplied nonnegative penalty. -/
def totalSplitCost (penalty : SplitEdge → ℝ) (e : SplitEdge) : ℝ :=
  (splitCost e : ℝ) + penalty e

theorem totalSplitCost_nonneg (penalty : SplitEdge → ℝ)
    (hpen : ∀ e, 0 ≤ penalty e) (e : SplitEdge) :
    0 ≤ totalSplitCost penalty e := by
  unfold totalSplitCost
  have hbase : 0 ≤ (splitCost e : ℝ) := Nat.cast_nonneg _
  nlinarith [hbase, hpen e]

/-! ### Structured penalty interface -/

/-- A penalty model is any split penalty proven nonnegative. -/
structure SplitPenalty where
  penalty : SplitEdge → ℝ
  nonneg : ∀ e, 0 ≤ penalty e

/-- Total cost induced by a structured penalty model. -/
def totalSplitCostP (P : SplitPenalty) (e : SplitEdge) : ℝ :=
  totalSplitCost P.penalty e

theorem totalSplitCostP_nonneg (P : SplitPenalty) (e : SplitEdge) :
    0 ≤ totalSplitCostP P e := by
  exact totalSplitCost_nonneg P.penalty P.nonneg e

/-! ## Weighted energy proxy (shell term + penalty)

To model the tradeoff between physical penalties (e.g. Coulomb/surface) and
shell/topological effects, we use a weighted objective:

`energyProxy lam penalty = penalty + lam · splitCost`.

This lets us prove conditional “peak” statements of the form:
if the penalty disadvantage of a magic fragment is not too large, then the
shell term dominates and the magic-fragment split wins.
-/

/-- Weighted objective: physical penalty plus shell-weighted (distance-to-magic) cost. -/
def energyProxy (lam : ℝ) (penalty : SplitEdge → ℝ) (e : SplitEdge) : ℝ :=
  penalty e + lam * (splitCost e : ℝ)

theorem energyProxy_le_of_penalty_le (lam : ℝ) (penalty : SplitEdge → ℝ) (e₁ e₂ : SplitEdge)
    (h : penalty e₁ ≤ penalty e₂ + lam * ((splitCost e₂ : ℝ) - (splitCost e₁ : ℝ))) :
    energyProxy lam penalty e₁ ≤ energyProxy lam penalty e₂ := by
  unfold energyProxy
  linarith

/-! ## Core attractor/minimum lemmas -/

/-- If both fragments are doubly-magic, split cost is zero. -/
theorem splitCost_zero_of_doublyMagic (e : SplitEdge)
    (hA : Nuclear.MagicNumbers.isDoublyMagic e.fragA.Z e.fragA.N)
    (hB : Nuclear.MagicNumbers.isDoublyMagic e.fragB.Z e.fragB.N) :
    splitCost e = 0 := by
  unfold splitCost
  rw [stabilityDistance_zero_of_doublyMagic e.fragA hA,
    stabilityDistance_zero_of_doublyMagic e.fragB hB]

/-- Any doubly-magic split is (parent-relative) cost-minimal among all splits of the same parent. -/
theorem splitCost_minimal_of_doublyMagic (e : SplitEdge)
    (hA : Nuclear.MagicNumbers.isDoublyMagic e.fragA.Z e.fragA.N)
    (hB : Nuclear.MagicNumbers.isDoublyMagic e.fragB.Z e.fragB.N) :
    ∀ other : SplitEdge, other.parent = e.parent → splitCost e ≤ splitCost other := by
  intro other _hparent
  have h0 : splitCost e = 0 := splitCost_zero_of_doublyMagic e hA hB
  rw [h0]
  exact Nat.zero_le _

/-- If the penalty is nonnegative and vanishes on a doubly-magic split,
then the doubly-magic split is cost-minimal (among splits of the same parent)
for the penalty-augmented objective. -/
theorem totalSplitCost_minimal_of_doublyMagic
    (penalty : SplitEdge → ℝ) (hpen : ∀ e, 0 ≤ penalty e)
    (e : SplitEdge)
    (hA : Nuclear.MagicNumbers.isDoublyMagic e.fragA.Z e.fragA.N)
    (hB : Nuclear.MagicNumbers.isDoublyMagic e.fragB.Z e.fragB.N)
    (hpen0 : penalty e = 0) :
    ∀ other : SplitEdge, other.parent = e.parent → totalSplitCost penalty e ≤ totalSplitCost penalty other := by
  intro other _hparent
  have h0 : splitCost e = 0 := splitCost_zero_of_doublyMagic e hA hB
  unfold totalSplitCost
  -- Left side reduces to 0.
  simp [h0, hpen0]
  -- Right side is nonnegative.
  exact totalSplitCost_nonneg penalty hpen other

/-- Structured-penalty version of `totalSplitCost_minimal_of_doublyMagic`. -/
theorem totalSplitCostP_minimal_of_doublyMagic
    (P : SplitPenalty)
    (e : SplitEdge)
    (hA : Nuclear.MagicNumbers.isDoublyMagic e.fragA.Z e.fragA.N)
    (hB : Nuclear.MagicNumbers.isDoublyMagic e.fragB.Z e.fragB.N)
    (hpen0 : P.penalty e = 0) :
    ∀ other : SplitEdge, other.parent = e.parent → totalSplitCostP P e ≤ totalSplitCostP P other := by
  intro other hparent
  unfold totalSplitCostP
  exact totalSplitCost_minimal_of_doublyMagic P.penalty P.nonneg e hA hB hpen0 other hparent

/-- Split cost is always nonnegative (trivial, but convenient for downstream proofs). -/
theorem splitCost_nonneg (e : SplitEdge) : 0 ≤ splitCost e := Nat.zero_le _

/-! ## A concrete peak-candidate example (purely in the proxy metric)

This is *not* a physical yield claim; it is a demonstration that, under the
baseline `splitCost`, a split producing the doubly-magic Sn-132 fragment can
out-rank a symmetric split for a representative parent.
-/

def Uranium236 : Node := ⟨92, 144⟩
def Tin132 : Node := ⟨50, 82⟩
def Molybdenum104 : Node := ⟨42, 62⟩
def SymmFrag : Node := ⟨46, 72⟩

def splitSn132 : SplitEdge where
  parent := Uranium236
  fragA := Tin132
  fragB := Molybdenum104
  conserves_Z := rfl
  conserves_N := rfl

def splitSymmetric : SplitEdge where
  parent := Uranium236
  fragA := SymmFrag
  fragB := SymmFrag
  conserves_Z := rfl
  conserves_N := rfl

theorem splitCost_sn132_lt_symmetric :
    splitCost splitSn132 < splitCost splitSymmetric := by
  native_decide

theorem splitCost_splitSn132 : splitCost splitSn132 = 20 := by
  native_decide

theorem splitCost_splitSymmetric : splitCost splitSymmetric = 28 := by
  native_decide

theorem energyProxy_sn132_le_symmetric (penalty : SplitEdge → ℝ) (lam : ℝ)
    (hpen : penalty splitSn132 ≤ penalty splitSymmetric + lam * 8) :
    energyProxy lam penalty splitSn132 ≤ energyProxy lam penalty splitSymmetric := by
  -- Reduce the generic comparison lemma to the concrete numeric splitCost gap (28 - 20 = 8).
  have hgap : (splitCost splitSymmetric : ℝ) - (splitCost splitSn132 : ℝ) = 8 := by
    -- Rewrite both costs to numerals and let `norm_num` compute.
    norm_num [splitCost_splitSn132, splitCost_splitSymmetric]
  apply energyProxy_le_of_penalty_le (lam := lam) (penalty := penalty) (e₁ := splitSn132) (e₂ := splitSymmetric)
  -- Turn the user-provided `+ λ*8` bound into the generic `+ λ*(ΔsplitCost)` bound.
  simpa [hgap]

/-! ### A simple explicit penalty: mass-imbalance

This penalty favors symmetric splits (smaller mass difference), which is a standard
baseline trend; the shell term (via `splitCost`) can overcome it when sufficiently weighted.
-/

def imbalancePenalty (k : ℝ) (e : SplitEdge) : ℝ :=
  k * |((e.fragA.massNumber : ℝ) - (e.fragB.massNumber : ℝ))|

theorem imbalancePenalty_nonneg (k : ℝ) (hk : 0 ≤ k) (e : SplitEdge) :
    0 ≤ imbalancePenalty k e := by
  unfold imbalancePenalty
  have habs : 0 ≤ |((e.fragA.massNumber : ℝ) - (e.fragB.massNumber : ℝ))| := by
    exact abs_nonneg _
  exact mul_nonneg hk habs

def imbalancePenaltyModel (k : ℝ) (hk : 0 ≤ k) : SplitPenalty where
  penalty := imbalancePenalty k
  nonneg := imbalancePenalty_nonneg k hk

theorem imbalancePenalty_splitSymmetric (k : ℝ) :
    imbalancePenalty k splitSymmetric = 0 := by
  -- Both fragments are identical, so the mass difference is zero.
  unfold imbalancePenalty splitSymmetric SymmFrag Uranium236
  -- `massNumber` reduces to `Z+N`, and the rest is arithmetic.
  norm_num [NuclearConfig.massNumber]

theorem imbalancePenalty_splitSn132 (k : ℝ) :
    imbalancePenalty k splitSn132 = k * 28 := by
  unfold imbalancePenalty splitSn132 Tin132 Molybdenum104 Uranium236
  norm_num [NuclearConfig.massNumber]

theorem energyProxy_sn132_le_symmetric_of_imbalance (k lam : ℝ)
    (h : k * 28 ≤ lam * 8) :
    energyProxy lam (imbalancePenalty k) splitSn132 ≤
      energyProxy lam (imbalancePenalty k) splitSymmetric := by
  apply energyProxy_sn132_le_symmetric (penalty := imbalancePenalty k) (lam := lam)
  -- Reduce the condition to the provided inequality `k*28 ≤ lam*8`.
  -- `imbalancePenalty splitSymmetric = 0`, so `+ lam*8` is exactly the shell gap term.
  simp [imbalancePenalty_splitSn132, imbalancePenalty_splitSymmetric, h]

/-! ### Another explicit penalty: charge-imbalance (Z-asymmetry)

This is a simplified Coulomb/symmetry proxy: it favors equal charge splits.
-/

def chargeImbalancePenalty (k : ℝ) (e : SplitEdge) : ℝ :=
  k * |((e.fragA.Z : ℝ) - (e.fragB.Z : ℝ))|

theorem chargeImbalancePenalty_nonneg (k : ℝ) (hk : 0 ≤ k) (e : SplitEdge) :
    0 ≤ chargeImbalancePenalty k e := by
  unfold chargeImbalancePenalty
  exact mul_nonneg hk (abs_nonneg _)

theorem chargeImbalancePenalty_splitSymmetric (k : ℝ) :
    chargeImbalancePenalty k splitSymmetric = 0 := by
  unfold chargeImbalancePenalty splitSymmetric SymmFrag Uranium236
  norm_num

theorem chargeImbalancePenalty_splitSn132 (k : ℝ) :
    chargeImbalancePenalty k splitSn132 = k * 8 := by
  unfold chargeImbalancePenalty splitSn132 Tin132 Molybdenum104 Uranium236
  norm_num

theorem energyProxy_sn132_le_symmetric_of_chargeImbalance (k lam : ℝ)
    (h : k * 8 ≤ lam * 8) :
    energyProxy lam (chargeImbalancePenalty k) splitSn132 ≤
      energyProxy lam (chargeImbalancePenalty k) splitSymmetric := by
  apply energyProxy_sn132_le_symmetric (penalty := chargeImbalancePenalty k) (lam := lam)
  simp [chargeImbalancePenalty_splitSn132, chargeImbalancePenalty_splitSymmetric, h]

end FragmentAttractors
end Fission
end IndisputableMonolith
