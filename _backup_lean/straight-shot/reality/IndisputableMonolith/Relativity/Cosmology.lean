-- Cosmology Module Aggregator
-- Layer 1: FRW basics
import IndisputableMonolith.Relativity.Cosmology.FRWMetric

-- Layer 2: Scalar field and Friedmann
import IndisputableMonolith.Relativity.Cosmology.ScalarOnFRW
import IndisputableMonolith.Relativity.Cosmology.Friedmann

-- Layer 3: Perturbations and Buchert averaging
import IndisputableMonolith.Relativity.Cosmology.Perturbations
import IndisputableMonolith.Relativity.Cosmology.Buchert

-- Layer 4: Growth and observables
import IndisputableMonolith.Relativity.Cosmology.GrowthFactor
import IndisputableMonolith.Relativity.Cosmology.Sigma8

-- Layer 5: ILG extensions (depends on ILG.Kernel)
import IndisputableMonolith.Relativity.Cosmology.BackgroundExtension
import IndisputableMonolith.Relativity.Cosmology.OpticalExtension

/-!
# Cosmology Module

Provides FRW cosmology with scalar field extensions:
- `FRWMetric` - FRW metric ds² = -dt² + a(t)² dx²
- `ScalarOnFRW` - Scalar field on FRW background
- `Friedmann` - Friedmann equations H² = 8πG/3 (ρ_m + ρ_ψ)
- `Perturbations` - Linear density perturbations δ
- `Buchert` - Buchert averaging formalism
- `GrowthFactor` - Growth function D(a)
- `Sigma8` - σ₈ amplitude calculation
- `BackgroundExtension` - ILG background cosmology
- `OpticalExtension` - ILG optical observables
-/
