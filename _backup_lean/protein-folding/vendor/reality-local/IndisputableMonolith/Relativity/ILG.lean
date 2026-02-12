-- ILG (Induced Light Gravity) Module Aggregator
-- Layer 1: Core action and parameters
import IndisputableMonolith.Relativity.ILG.Action
import IndisputableMonolith.Relativity.ILG.Params
import IndisputableMonolith.Relativity.ILG.Falsifiers

-- Layer 2: Variation and FRW cosmology
import IndisputableMonolith.Relativity.ILG.Variation
import IndisputableMonolith.Relativity.ILG.FRW
import IndisputableMonolith.Relativity.ILG.FRWDerive

-- Layer 3: Compact objects and GW
import IndisputableMonolith.Relativity.ILG.Compact
import IndisputableMonolith.Relativity.ILG.BHDerive
import IndisputableMonolith.Relativity.ILG.GW
import IndisputableMonolith.Relativity.ILG.GWDerived

-- Layer 4: Growth and cosmology derived
import IndisputableMonolith.Relativity.ILG.Growth
import IndisputableMonolith.Relativity.ILG.CosmologyDerived

-- Layer 5: PPN framework
import IndisputableMonolith.Relativity.ILG.PPN
import IndisputableMonolith.Relativity.ILG.PPNDerive
import IndisputableMonolith.Relativity.ILG.PPNDerived

-- Layer 6: Weak field and linearization
import IndisputableMonolith.Relativity.ILG.WeakField
import IndisputableMonolith.Relativity.ILG.WeakFieldDerived
import IndisputableMonolith.Relativity.ILG.Linearize
import IndisputableMonolith.Relativity.ILG.KernelForm

-- Layer 7: Lensing
import IndisputableMonolith.Relativity.ILG.Lensing
import IndisputableMonolith.Relativity.ILG.LensingDerived

-- Layer 8: Substrate (quantum connection)
import IndisputableMonolith.Relativity.ILG.Substrate

/-!
# Induced Light Gravity (ILG) Module

The complete ILG theory framework:

## Core Theory (Layer 1-2)
- `Action` - ILG action S = ∫ (R + α ψ R + ...) √-g d⁴x
- `Params` - (α, C_lag) parameter space
- `Falsifiers` - Theory falsification conditions
- `Variation` - Field equations from action variation

## Compact Objects (Layer 3)
- `Compact` - Static spherical solutions
- `BHDerive` - Black hole solutions
- `GW` - Gravitational wave production
- `GWDerived` - GW propagation effects

## Cosmology (Layer 4-5)
- `FRW` - FRW cosmology in ILG
- `FRWDerive` - Friedmann equations
- `Growth` - Structure growth D(a)
- `CosmologyDerived` - σ₈, S₈ predictions

## PPN Framework (Layer 5-6)
- `PPN` - Post-Newtonian parameters
- `PPNDerive` - γ, β extraction
- `PPNDerived` - Solar system constraints

## Weak Field (Layer 6-7)
- `WeakField` - Weak field approximation
- `WeakFieldDerived` - Modified Poisson derivation
- `Linearize` - Linearized equations
- `KernelForm` - Weight kernel representation

## Lensing (Layer 7)
- `Lensing` - Gravitational lensing in ILG
- `LensingDerived` - Lensing observables

## Quantum Foundation (Layer 8)
- `Substrate` - Connection to quantum substrate
-/
