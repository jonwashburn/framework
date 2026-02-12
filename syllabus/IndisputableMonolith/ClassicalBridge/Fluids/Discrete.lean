import Mathlib

namespace IndisputableMonolith
namespace ClassicalBridge
namespace Fluids

/-!
# Fluids Bridge: Discrete model interface

This file deliberately does **not** pick a discretization yet (Galerkin vs grid).
It defines the minimal interface we need for a discrete Navier–Stokes approximation
that we can later relate to:

- an LNAL spatial execution semantics, and
- a CPM instantiation (defect/energy/tests).

Downstream files should introduce concrete models (e.g. Galerkin on `𝕋^2` first).
-/

/-- Parameters for incompressible Navier–Stokes (dimension + viscosity). -/
structure NSParams where
  /-- Spatial dimension (use 2 first, then lift to 3). -/
  d : ℕ := 3
  /-- Kinematic viscosity. -/
  ν : ℝ := 1

/-- Validity predicate for parameters (keep proofs out of the structure to avoid hidden coercions). -/
def NSParams.Valid (p : NSParams) : Prop :=
  0 < p.ν ∧ 2 ≤ p.d

/-- A discrete time step (Δt > 0). -/
structure TimeStep where
  Δt : ℝ := 1

def TimeStep.Valid (h : TimeStep) : Prop := 0 < h.Δt

/-- High-level choice of discretization family. -/
inductive DiscretizationKind where
  | spectralGalerkin
  | finiteDifference
deriving DecidableEq

/-- A discrete dynamical model intended to approximate NS. -/
structure DiscreteModel where
  /-- State type (e.g. truncated Fourier coefficients). -/
  State : Type
  /-- Tag: Galerkin vs grid, etc. -/
  kind : DiscretizationKind
  /-- One (discrete) time step of the model. -/
  step : NSParams → TimeStep → State → State

/-- Optional energy functional on the discrete state (used for a priori bounds). -/
structure EnergyFunctional (D : DiscreteModel) where
  E : D.State → ℝ

end Fluids
end ClassicalBridge
end IndisputableMonolith
