import IndisputableMonolith.Constants

/-!
# IndisputableMonolith (umbrella module)

This file exists as a lightweight umbrella module so that Lake can build the
`IndisputableMonolith` library target cleanly when a root module is requested.

It intentionally imports only the most central, dependency-light submodule.
Downstream code should prefer importing specific modules (e.g.
`IndisputableMonolith.Constants`, `IndisputableMonolith.Masses.*`, etc.) to keep
import closures small and auditable.
-/
