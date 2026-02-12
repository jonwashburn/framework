/-!
# IndisputableMonolith

Project facade module.

This repo historically referenced a top-level `IndisputableMonolith` module.
We keep this file intentionally *minimal* and focused; downstream files should
prefer importing the specific submodules they require.

We intentionally do **not** re-export subtheories here to avoid cyclic
dependencies in the build graph. Prefer importing, e.g.:
- `IndisputableMonolith.Flight`
- `IndisputableMonolith.Spiral.SpiralField`
-/

