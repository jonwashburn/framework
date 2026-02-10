import Mathlib
import IndisputableMonolith.Relativity.Geometry.MatrixBridge
import IndisputableMonolith.Relativity.Geometry.Tensor
import IndisputableMonolith.Relativity.Geometry.Manifold
import IndisputableMonolith.Relativity.ILG.WeakField
import IndisputableMonolith.Relativity.ILG.WeakFieldDerived
import IndisputableMonolith.Relativity.ILG.PPN
import IndisputableMonolith.Relativity.ILG.PPNDerive
import IndisputableMonolith.Relativity.ILG.FRW
import IndisputableMonolith.Relativity.ILG.Params

/-!
# Relativity umbrella module

Re-exports the Relativity stack so higher-level modules can simply `import
IndisputableMonolith.Relativity` without re-introducing circular dependencies.
All substantive content lives in the files under `Relativity/`; this file
exists purely as a convenience shim.
-/
