import Mathlib
import IndisputableMonolith.Fusion.NuclearBridge
import IndisputableMonolith.Fission.FragmentAttractors
import IndisputableMonolith.Fission.BarrierLandscape

/-!
# Spontaneous Fission Stability Ranking (FI4)

This module produces a **certified proxy** for ranking spontaneous fission
(SF) stability. The proxy captures the qualitative behavior: nuclei farther
from magic closures have lower barriers and shorter half-lives.

## Core Model

We define a **barrier proxy** based on:
1. `stabilityDistance` — topological distance-to-magic term.
2. An optional physics-layer baseline (Coulomb/surface) that we track as a
   hypothesis.

Under explicit assumptions, we prove **monotonicity**: increasing stability
distance decreases the barrier proxy (i.e., makes the nucleus less stable
against SF).

Part of: `planning/FUSION_FISSION_RESEARCH_EXECUTION_PLAN.md` Phase 10 (FI4).
-/

namespace IndisputableMonolith
namespace Fission
namespace SpontaneousFissionRanking

open Fusion.NuclearBridge
open BarrierLandscape

/-! ## Barrier Proxy Definition -/

/-- A ranking model for spontaneous fission:
    * `barrierScale` converts stabilityDistance into an energy-scale term
    * `baseline` is a physics-layer baseline barrier (hypothesized nonnegative)
-/
structure SFRankingModel where
  /-- Converts stability distance into a barrier contribution (positive → higher barrier). -/
  barrierScale : ℝ
  barrierScale_pos : 0 < barrierScale
  /-- Baseline barrier (from Coulomb/surface terms), assumed nonnegative. -/
  baseline : ℕ → ℕ → ℝ  -- Z, N → baseline barrier
  baseline_nonneg : ∀ Z N, 0 ≤ baseline Z N

/-- The barrier proxy for a given nucleus: higher value = more stable against SF.
    barrierProxy = baseline(Z,N) + barrierScale × (maxStabilityDistance − stabilityDistance)

    We use a "flipped" form so that *increasing* stabilityDistance *decreases*
    the proxy (i.e., less stable).
-/
noncomputable def barrierProxy (M : SFRankingModel) (cfg : NuclearConfig) (maxDist : ℕ) : ℝ :=
  M.baseline cfg.Z cfg.N + M.barrierScale * (maxDist - stabilityDistance cfg : ℝ)

/-- Alternative: instability proxy = baseline' − barrierScale × stabilityDistance.
    Higher stabilityDistance ↦ higher instability. -/
noncomputable def instabilityProxy (M : SFRankingModel) (cfg : NuclearConfig) : ℝ :=
  M.barrierScale * (stabilityDistance cfg : ℝ) - M.baseline cfg.Z cfg.N

/-! ## Monotonicity Theorems -/

/-- If two nuclei have the same baseline, then the one with lower stability distance
    has a higher barrier proxy (more stable). -/
theorem barrierProxy_monotone (M : SFRankingModel) (cfgA cfgB : NuclearConfig) (maxDist : ℕ)
    (hSameBase : M.baseline cfgA.Z cfgA.N = M.baseline cfgB.Z cfgB.N)
    (hDistLt : stabilityDistance cfgA < stabilityDistance cfgB) :
    barrierProxy M cfgB maxDist < barrierProxy M cfgA maxDist := by
  unfold barrierProxy
  rw [hSameBase]
  have hScale := M.barrierScale_pos
  have hGap : (stabilityDistance cfgA : ℝ) < (stabilityDistance cfgB : ℝ) := by
    exact Nat.cast_lt.mpr hDistLt
  -- maxDist - S_A > maxDist - S_B when S_A < S_B
  nlinarith

/-- Stability distance zero (doubly-magic) achieves maximal barrier proxy
    (among nuclei with the same baseline and same maxDist). -/
theorem doublyMagic_max_barrier (M : SFRankingModel) (cfg : NuclearConfig) (maxDist : ℕ)
    (hDM : Nuclear.MagicNumbers.isDoublyMagic cfg.Z cfg.N) :
    barrierProxy M cfg maxDist = M.baseline cfg.Z cfg.N + M.barrierScale * (maxDist : ℝ) := by
  unfold barrierProxy
  have h0 : stabilityDistance cfg = 0 := stabilityDistance_zero_of_doublyMagic cfg hDM
  simp [h0]

/-! ## Ranking Comparison -/

/-- Two nuclei can be ranked by their barrier proxy. -/
def isMoreStable (M : SFRankingModel) (cfgA cfgB : NuclearConfig) (maxDist : ℕ) : Prop :=
  barrierProxy M cfgA maxDist ≥ barrierProxy M cfgB maxDist

/-- Stability ranking: lower stability distance + same baseline ⟹ more stable. -/
theorem ranking_by_distance (M : SFRankingModel) (cfgA cfgB : NuclearConfig) (maxDist : ℕ)
    (hSameBase : M.baseline cfgA.Z cfgA.N = M.baseline cfgB.Z cfgB.N)
    (hDistLe : stabilityDistance cfgA ≤ stabilityDistance cfgB) :
    isMoreStable M cfgA cfgB maxDist := by
  unfold isMoreStable barrierProxy
  rw [hSameBase]
  have hScale := M.barrierScale_pos
  have hGap : (stabilityDistance cfgA : ℝ) ≤ (stabilityDistance cfgB : ℝ) := by
    exact Nat.cast_le.mpr hDistLe
  nlinarith

/-! ## Concrete Example: Cf-252 vs Fm-256 -/

def Californium252 : NuclearConfig := ⟨98, 154⟩
def Fermium256 : NuclearConfig := ⟨100, 156⟩

/-- Cf-252 stability distance (computed).
    Z=98: distToMagic 98 = min{|98-82|, |98-126|} = 16
    N=154: distToMagic 154 = |154-126| = 28
    Total = 16 + 28 = 44 -/
theorem cf252_stabilityDistance : stabilityDistance Californium252 = 44 := by native_decide

/-- Fm-256 stability distance (computed).
    Z=100: distToMagic 100 = min{|100-82|, |100-126|} = 18
    N=156: distToMagic 156 = |156-126| = 30
    Total = 18 + 30 = 48 -/
theorem fm256_stabilityDistance : stabilityDistance Fermium256 = 48 := by native_decide

/-- Cf-252 has lower stability distance than Fm-256 (and thus higher barrier proxy
    under equal baseline). -/
theorem cf252_more_stable_than_fm256_cond (M : SFRankingModel) (maxDist : ℕ)
    (hSameBase : M.baseline 98 154 = M.baseline 100 156) :
    isMoreStable M Californium252 Fermium256 maxDist := by
  apply ranking_by_distance M Californium252 Fermium256 maxDist hSameBase
  -- stabilityDistance Cf-252 = 44 ≤ 48 = stabilityDistance Fm-256
  native_decide

/-! ## Soundness Statement -/

/-- **Soundness**: the ranking proxy is consistent with the qualitative physics.
    If a nucleus is closer to magic closures, it has a higher barrier and is
    more stable against SF (under explicit hypotheses). -/
theorem ranking_soundness (M : SFRankingModel) (cfgA cfgB : NuclearConfig) (maxDist : ℕ)
    (hSameBase : M.baseline cfgA.Z cfgA.N = M.baseline cfgB.Z cfgB.N)
    (hDistLe : stabilityDistance cfgA ≤ stabilityDistance cfgB) :
    isMoreStable M cfgA cfgB maxDist :=
  ranking_by_distance M cfgA cfgB maxDist hSameBase hDistLe

end SpontaneousFissionRanking
end Fission
end IndisputableMonolith
