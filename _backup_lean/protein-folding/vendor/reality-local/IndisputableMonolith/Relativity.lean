import Mathlib

-- ==========================================================================
-- Foundation Layer: Geometry, Calculus, Fields, Variation
-- ==========================================================================
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Calculus
import IndisputableMonolith.Relativity.Fields
import IndisputableMonolith.Relativity.Variation
import IndisputableMonolith.Relativity.Analysis

-- ==========================================================================
-- Perturbation Theory (Track 3)
-- ==========================================================================
import IndisputableMonolith.Relativity.Perturbation

-- ==========================================================================
-- Post-Newtonian Approximation
-- ==========================================================================
import IndisputableMonolith.Relativity.PostNewtonian

-- ==========================================================================
-- Geodesics and Lensing
-- ==========================================================================
import IndisputableMonolith.Relativity.Geodesics
import IndisputableMonolith.Relativity.Lensing

-- ==========================================================================
-- Gravitational Waves
-- ==========================================================================
import IndisputableMonolith.Relativity.GW

-- ==========================================================================
-- Compact Objects
-- ==========================================================================
import IndisputableMonolith.Relativity.Compact

-- ==========================================================================
-- Cosmology
-- ==========================================================================
import IndisputableMonolith.Relativity.Cosmology

-- ==========================================================================
-- ILG Theory (Induced Light Gravity)
-- ==========================================================================
import IndisputableMonolith.Relativity.ILG

-- ==========================================================================
-- GR Limit Analysis
-- ==========================================================================
import IndisputableMonolith.Relativity.GRLimit

-- ==========================================================================
-- ILG Core Theorems (from top-level ILG/)
-- ==========================================================================
import IndisputableMonolith.ILG.Reciprocity
import IndisputableMonolith.ILG.GrowthODE
import IndisputableMonolith.ILG.ISWSign
import IndisputableMonolith.ILG.PoissonKernel

/-!
# Relativity Umbrella Module

Re-exports the complete Relativity stack for convenient imports.

## Module Structure

### Foundation
- `Geometry` - Manifold, metric, connection, curvature tensors
- `Calculus` - Partial derivatives, Laplacian, D'Alembertian
- `Fields` - Scalar field, gradient, stress-energy
- `Variation` - Action functionals, Einstein equations
- `Analysis` - Landau notation, limits

### Perturbation Theory
- `Perturbation` - Full linearized GR with scalar field (19 submodules)

### Post-Newtonian
- `PostNewtonian` - 1PN expansion, PPN parameters γ, β

### Geodesics & Lensing
- `Geodesics` - Null geodesic equations
- `Lensing` - Deflection angles, time delays

### Gravitational Waves
- `GW` - Tensor perturbations, propagation speed c_T

### Compact Objects
- `Compact` - Static spherical solutions

### Cosmology
- `Cosmology` - FRW, Friedmann, perturbations, σ₈

### ILG Theory
- `ILG` - Complete Induced Light Gravity framework (22 submodules)

### GR Limit
- `GRLimit` - Smooth reduction to GR as (α, C_lag) → 0

### Core ILG Theorems
- `Reciprocity`, `GrowthODE`, `ISWSign`, `PoissonKernel`
-/
