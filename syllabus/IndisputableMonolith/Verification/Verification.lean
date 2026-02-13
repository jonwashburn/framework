import IndisputableMonolith.Verification

/-!
# `Verification.Verification` (Deprecated Compatibility Shim)

This module previously duplicated declarations from `IndisputableMonolith/Verification.lean`
inside the **same namespace** `IndisputableMonolith.Verification`, which could cause
environment collisions and silently reintroduce trivial “gate” stubs.

It is now a thin shim that simply re-exports the canonical module.
-/
