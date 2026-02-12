import IndisputableMonolith.LNAL
import IndisputableMonolith.PNAL
import IndisputableMonolith.LightLanguage.WTokens
import IndisputableMonolith.LightLanguage.WTokenSemantics

/-!
# IndisputableMonolith.LightLanguage (compatibility facade)

`Source-Super-rrf.txt` and some older paper/spec language refer to a
`LightLanguage` / "ULL" layer.

In the current Lean codebase, the executable language layer is organized as:
- `IndisputableMonolith.PNAL` (front-end syntax/compilation)
- `IndisputableMonolith.LNAL` (typed VM, schedules, invariants)

This file is a **thin facade** to reduce naming drift while the "Octave System"
formalization is being built. It does not introduce new claims or definitions.

## Submodules

- `LightLanguage.WTokens`: Aliases for WToken types from `Water.WTokenIso`
- `LightLanguage.WTokenSemantics`: WToken interpretation layer on LNAL primitives
  (maps WTokens to LNAL instruction sequences, phase signatures, and coupling patterns)
-/
