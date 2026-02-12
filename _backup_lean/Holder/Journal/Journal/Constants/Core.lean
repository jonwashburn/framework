/-!
# Core Constants

All constants in this module are derived from the Golden Ratio φ.
No free parameters. No magic numbers.

## RS-Native Units
- τ₀ = 1 tick (fundamental time quantum)
- ℓ₀ = 1 voxel (fundamental length quantum)
- c = 1 voxel/tick (speed of light in RS units)
-/

namespace Journal.Constants

/-- The Golden Ratio φ = (1 + √5) / 2.
    This is the seed of all derived constants. -/
noncomputable def phi : Float := (1 + Float.sqrt 5) / 2

/-- The fundamental time unit τ₀ (RS-native). -/
def tau0 : Float := 1.0

/-- The fundamental length unit ℓ₀ (RS-native). -/
def ell0 : Float := 1.0

/-- Speed of light c = 1 voxel/tick (RS-native). -/
def c : Float := 1.0

/-- Coherence energy E_coh = φ⁻⁵ (RS-native). -/
noncomputable def E_coh : Float := phi ^ (-5 : Float)

/-- The locked fine-structure constant α_lock = (1 − 1/φ) / 2. -/
noncomputable def alpha_lock : Float := (1 - 1 / phi) / 2

/-- The 8-tick octave period. -/
def octave : Float := 8.0

end Journal.Constants
