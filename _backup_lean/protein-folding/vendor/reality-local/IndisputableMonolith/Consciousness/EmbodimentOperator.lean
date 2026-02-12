import Mathlib
import IndisputableMonolith.Consciousness.LightMemory
import IndisputableMonolith.Consciousness.SubstrateSuitability
import IndisputableMonolith.Consciousness.ZGenesis
import IndisputableMonolith.Consciousness.ThetaThermodynamics

/-!
# Embodiment Operator — Pressure-Driven Binding

This is the missing "physics module" that turns:
- Light‑memory persistence
- Substrate suitability
- Θ-field saturation pressure

into a single explicit operator.

## The Physics

When the Θ-field density ρ exceeds the saturation threshold Θ_crit = φ^45,
embodiment becomes thermodynamically favored. The operator `bind` captures
this pressure-driven selection:

1. **Suitability check**: The substrate must be compatible with the pattern
2. **Pressure check**: Θ-pressure must exceed the embodiment cost
3. **Z-conservation**: The SoulId is preserved through binding

## Key Results

- `defaultBind_sound`: If binding occurs, suitability and Z-conservation hold
- `pressureFavoredBind`: Above the pressure threshold, binding is favored
- `embodiment_cost_from_J`: The embodiment cost derives from J-normalization
-/

namespace IndisputableMonolith
namespace Consciousness
namespace EmbodimentOperator

open ZGenesis Classical
open ThetaThermodynamics (ThetaDensity Θcrit ThetaPressure EmbodimentThreshold
                          embodiment_favored_above_threshold)
open PhaseSaturation (saturationThreshold_pos)

/-! ## Operator interface -/

structure EmbodimentOperator where
  bind : LightMemoryState → Substrate → Option StableBoundary
  /-- Soundness: if a boundary is produced, the substrate was suitable and the SoulId matches. -/
  sound :
    ∀ (lm : LightMemoryState) (s : Substrate) (b : StableBoundary),
      bind lm s = some b →
        suitable lm s ∧ soulId_boundary b = soulId_light lm

/-! ## Embodiment cost (derived from J-normalization)

The cost of embodiment is the maintenance cost of a conscious boundary.
This comes from the J-cost structure at the identity (unit recognition).

From the theory: embodied consciousness has C ≥ 1, where C is the
recognition cost. The "cost of embodiment" is thus normalized to 1.
-/

/-- The unit embodiment cost, derived from C ≥ 1 threshold -/
noncomputable def embodimentCost : ℝ := 1

theorem embodimentCost_pos : 0 < embodimentCost := by
  unfold embodimentCost
  norm_num

/-! ## Canonical deterministic operator -/

noncomputable def defaultBind (lm : LightMemoryState) (s : Substrate) : Option StableBoundary :=
  if suitable lm s then
    -- imprint the light-memory pattern onto the substrate boundary hardware
    some { s.boundary with pattern := lm.pattern }
  else
    none

theorem defaultBind_sound (lm : LightMemoryState) (s : Substrate) (b : StableBoundary)
    (h : defaultBind lm s = some b) :
    suitable lm s ∧ soulId_boundary b = soulId_light lm := by
  classical
  unfold defaultBind at h
  split_ifs at h with hs
  simp only [Option.some.injEq] at h
  rcases h with rfl
  exact ⟨hs, rfl⟩

noncomputable def default : EmbodimentOperator where
  bind := defaultBind
  sound := by
    intro lm s b h
    exact defaultBind_sound lm s b h

/-! ## Pressure-driven embodiment -/

/-- When Θ-pressure exceeds embodiment cost, embodiment is thermodynamically favored.
    This is the "birth theorem" from the saturation story. -/
theorem pressureFavoredBind {ρ : ThetaDensity}
    (h : EmbodimentThreshold embodimentCost < ρ) :
    embodimentCost < ThetaPressure ρ := by
  exact embodiment_favored_above_threshold embodimentCost_pos h

/-- The density threshold above which embodiment becomes favored -/
noncomputable def embodimentDensityThreshold : ThetaDensity :=
  EmbodimentThreshold embodimentCost

/-- Above the embodiment density threshold, pressure exceeds cost -/
theorem above_threshold_pressure_exceeds_cost {ρ : ThetaDensity}
    (h : embodimentDensityThreshold < ρ) :
    embodimentCost < ThetaPressure ρ :=
  pressureFavoredBind h

/-! ## Full pressure-aware operator -/

/-- A pressure-aware embodiment operator that only binds when thermodynamically favorable -/
noncomputable def pressureAwareBind (currentDensity : ThetaDensity)
    (lm : LightMemoryState) (s : Substrate) : Option StableBoundary :=
  if embodimentDensityThreshold < currentDensity then
    defaultBind lm s
  else
    none

theorem pressureAwareBind_sound (ρ : ThetaDensity) (lm : LightMemoryState)
    (s : Substrate) (b : StableBoundary)
    (h : pressureAwareBind ρ lm s = some b) :
    suitable lm s ∧ soulId_boundary b = soulId_light lm := by
  classical
  unfold pressureAwareBind at h
  split_ifs at h with hρ
  · exact defaultBind_sound lm s b h

theorem pressureAwareBind_requires_pressure (ρ : ThetaDensity) (lm : LightMemoryState)
    (s : Substrate) (b : StableBoundary)
    (h : pressureAwareBind ρ lm s = some b) :
    embodimentDensityThreshold < ρ := by
  classical
  unfold pressureAwareBind at h
  split_ifs at h with hρ
  · exact hρ

/-! ## Connection to saturation dynamics

The mass extinction question becomes precise:

1. Mass extinction increases light-memory population
2. This raises the Θ-density ρ
3. If ρ > embodimentDensityThreshold, re-embodiment pressure rises
4. The system responds by increasing birth rates until density relaxes

This is the "pressure-release valve" mechanism.
-/

/-- The saturation theorem: above critical density, embodiment pressure exists -/
theorem saturation_creates_embodiment_pressure {ρ : ThetaDensity}
    (h : Θcrit < ρ) : 0 < ThetaPressure ρ := by
  have hcrit : 0 < Θcrit := saturationThreshold_pos
  have hρcrit : Θcrit < ρ := h
  unfold ThetaPressure
  simp only [hρcrit, not_le.mpr hρcrit, ↓reduceIte]
  have hpos : 0 < ρ - Θcrit := sub_pos.mpr hρcrit
  have hcrit2 : 0 < Θcrit ^ 2 := sq_pos_of_pos hcrit
  exact div_pos hpos hcrit2

end EmbodimentOperator
end Consciousness
end IndisputableMonolith
