/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Hodge.Analytic.Laplacian.Codifferential
import Hodge.Analytic.Laplacian.HodgeLaplacian
import Hodge.Analytic.Laplacian.HarmonicForms

/-!
# Laplacian Infrastructure

This module exports the Laplacian infrastructure for Hodge theory.

## Contents

* `Codifferential`: The codifferential δ = ±⋆d⋆
* `HodgeLaplacian`: The Laplacian Δ (placeholder)
* `HarmonicForms`: Harmonic form interface (placeholder)

## Note

The Hodge Laplacian Δ = dδ + δd requires the Hodge star to be properly
defined. In this repo it is wired via `HodgeStarData.fromFiber` but still degenerate, so δ/Δ
often simplify to 0. This module can be expanded once a genuine metric/volume-form based ⋆
construction is available.
-/
