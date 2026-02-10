import IndisputableMonolith.OctaveKernel

/-!
# IndisputableMonolith.RRF (compatibility facade)

Historical documents/specs in this repo reference an `RRF` namespace/directory
for the “Reality Recognition Framework”.

In the current repo snapshot, the dedicated `IndisputableMonolith/RRF/…` tree
is not present. The new `IndisputableMonolith.OctaveKernel` is intended to be
the minimal shared abstraction layer for the “Octave System” going forward.

This module is therefore a **thin facade**:
- it re-exports the kernel so older references can be updated incrementally,
- it introduces **no** new definitions, theorems, or empirical claims.
-/
