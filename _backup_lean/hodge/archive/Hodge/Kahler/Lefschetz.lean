/-
Copyright (c) 2026 Hodge Formalization Project. All rights reserved.
Released under Apache 2.0 license.
Authors: Agent 2 (Integration Theory)
-/
import Hodge.Kahler.Lefschetz.PrimitiveDecomp

/-!
# Lefschetz Theory Module

This module exports all Lefschetz theory files:

* `PrimitiveDecomp.lean`: Primitive decomposition and sl(2) relations

## Overview

The Lefschetz theory on Kähler manifolds involves:

1. **Lefschetz operators**: L (cup with ω), Λ (dual), H (weight)
2. **sl(2) representation**: L, Λ, H form an sl(2)-representation on cohomology
3. **Primitive decomposition**: H^k = ⊕_r L^r(P^{k-2r})
4. **Hard Lefschetz**: L^{n-k} : H^k → H^{2n-k} is bijective

## References

* [Griffiths-Harris, "Principles of Algebraic Geometry", Ch. 0, §6-7]
* [Voisin, "Hodge Theory and Complex Algebraic Geometry I", Ch. 6]
-/
