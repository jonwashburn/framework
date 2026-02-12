/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Filtration infrastructure for Hodge theory.

This module collects the categorical infrastructure for decreasing filtrations
following Deligne's *Théorie de Hodge II*.

Main components:
- `DecFiltration`: Decreasing ℤ-indexed filtrations
- `FilteredObject`: Category of filtered objects
- `BifilteredObject`: Objects with two filtrations
- `IsNOpposed`: n-opposed filtrations (Deligne 1.2.3)
- `gr`, `gr₂`, `grGr`: Associated graded pieces

These definitions support:
- The Hodge filtration F on H^n(X, ℂ)
- The conjugate filtration F̄
- The weight filtration W (for mixed Hodge structures)
- The canonical n-opposition: F and F̄ are n-opposed on H^n
-/

import Hodge.CategoryTheory.Filtration.Basic
import Hodge.CategoryTheory.Filtration.Opposed
import Hodge.CategoryTheory.Filtration.InducedOnGr
