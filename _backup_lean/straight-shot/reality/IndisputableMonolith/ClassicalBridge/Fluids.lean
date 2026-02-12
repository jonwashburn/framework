import IndisputableMonolith.ClassicalBridge.Fluids.RSImports
import IndisputableMonolith.ClassicalBridge.Fluids.BasicDefinitions
import IndisputableMonolith.ClassicalBridge.Fluids.GeometricDepletion
import IndisputableMonolith.ClassicalBridge.Fluids.RSClassicalBridge
import IndisputableMonolith.ClassicalBridge.Fluids.MainTheorem
import IndisputableMonolith.ClassicalBridge.Fluids.Bridge
import IndisputableMonolith.ClassicalBridge.Fluids.CPM
import IndisputableMonolith.ClassicalBridge.Fluids.CPM2D
import IndisputableMonolith.ClassicalBridge.Fluids.ContinuumLimit2D
import IndisputableMonolith.ClassicalBridge.Fluids.Discrete
import IndisputableMonolith.ClassicalBridge.Fluids.Galerkin2D
import IndisputableMonolith.ClassicalBridge.Fluids.LNAL
import IndisputableMonolith.ClassicalBridge.Fluids.LNALSemantics
import IndisputableMonolith.ClassicalBridge.Fluids.Regularity2D
import IndisputableMonolith.ClassicalBridge.Fluids.Simulation2D

/-!
# ClassicalBridge.Fluids (index)

This file provides a stable import surface for the RS↔Navier–Stokes bridge work.

## Module Structure

- `RSImports`: Recognition Science constants (φ, τ₀, C_star, cascade_cutoff, etc.)
- `BasicDefinitions`: Vector fields, PDE operators, NSE structure
- `GeometricDepletion`: Constantin-Fefferman mechanism (core depletion result)
- `RSClassicalBridge`: RS insights translated to classical bounds
- `MainTheorem`: Final global regularity theorem

## Port Status

All modules under `IndisputableMonolith/ClassicalBridge/Fluids/` currently build with **no `sorry`**
and **no `axiom`** (as of 2025-12-18).
-/
