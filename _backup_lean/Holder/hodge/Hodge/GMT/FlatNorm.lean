/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Hodge.GMT.FlatNormTopology

/-!
# GMT: Flat norm (wrapper)

The flat norm is implemented in `Hodge/Analytic/FlatNorm.lean` and re-exported in the planned GMT
module hierarchy via `Hodge/GMT/FlatNormTopology.lean`.

This file keeps the historical module name `Hodge.GMT.FlatNorm` available as a thin import layer,
without maintaining a parallel stubbed definition of the flat norm.
-/

noncomputable section

open Classical

set_option autoImplicit false

-- No additional declarations: importing this module brings `Hodge.GMT.flatNormReal` and
-- `Hodge.GMT.flatNorm` into scope from `Hodge.GMT.FlatNormTopology`.
