/-
# Goldbach Conjecture Formalization

This library formalizes the circle-method approach to Goldbach's conjecture
using a mod-8 periodic kernel.

## Structure

* `Goldbach.CircleMethod` - Main proof framework with mod-8 kernel

## Status

The formalization identifies exactly which mathematical work remains:
- The medium-arc L^4 saving (MED-L4 hypothesis) is the key bottleneck
- Unconditional results: density-one positivity, short-interval positivity
- Conditional results: uniform pointwise positivity (needs MED-L4)

See `Goldbach/CircleMethod.lean` for the detailed proof skeleton.
-/

import Goldbach.CircleMethod
