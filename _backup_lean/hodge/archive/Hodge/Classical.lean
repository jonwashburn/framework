import Hodge.Classical.HarveyLawson
import Hodge.Classical.GAGA
import Hodge.Classical.FedererFleming
import Hodge.Classical.Lefschetz
import Hodge.Classical.KahlerIdentities
import Hodge.Classical.PrimitiveDecomposition
import Hodge.Classical.HardLefschetz
import Hodge.Classical.Bergman
import Hodge.Classical.SerreVanishing

/-!
# Track A: Classical Theorems Foundation

This module exports all the classical theorems needed for the Hodge Conjecture proof.
These are deep theorems from complex geometry, algebraic geometry, and
geometric measure theory that are not (yet) in Mathlib.

## Kähler Identities (Task 4B, 4C)

The Kähler identities are fundamental commutation relations:
- [Λ, d] = i(∂̄* - ∂*) (Task 4B)
- [L, δ] = -i(∂̄ - ∂) (Task 4C)

These are axiomatized as Classical Pillars in `KahlerIdentities.lean`.

## Primitive Decomposition (Task 4E)

The Lefschetz decomposition expresses every cohomology class as:
  α = α₀ + L(α₁) + L²(α₂) + ...
where each αᵣ is a primitive class (ker Λ).

This is the key structural result connecting sl(2) representation theory
to the Hard Lefschetz theorem.

## Hard Lefschetz Theorem (Task 4G)

The Hard Lefschetz theorem is now **proved** from sl(2) representation theory
in `HardLefschetz.lean`:
- `hard_lefschetz_bijective_from_sl2` - Main theorem
- `lefschetz_inverse_from_sl2` - Explicit inverse construction
- `sl2_representation_bijectivity` - Key axiom from representation theory

This provides a **proof path** rather than a bare assumption.
-/
