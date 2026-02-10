import Hodge.Classical.GAGA

/-!
# Algebraic Geometry: GAGA (wrapper)

The repository currently encodes much of the “GAGA / Chow” interface in
`Hodge/Classical/GAGA.lean` (conceptual algebraic sets, and the analytic/algebraic bridge
as an inductive API).

The updated operational plan allocates a dedicated algebraic-geometry namespace under
`Hodge/AlgGeom/`.  This file provides the planned module path `Hodge.AlgGeom.GAGA` while
reusing the existing `Hodge.Classical.GAGA` development.
-/

noncomputable section

open Classical

set_option autoImplicit false

namespace Hodge.AlgGeom

-- This module currently serves as an import-location wrapper; definitions live in
-- `Hodge/Classical/GAGA.lean`.

end Hodge.AlgGeom
