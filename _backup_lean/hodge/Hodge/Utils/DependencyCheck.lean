import Hodge.Main

/-!
# Dependency Check Utility

This file prints the axioms used by the **data‑first** main theorem
`hodge_conjecture_data`. The legacy compatibility variant is intentionally
not checked here.

## Usage

Run with `lake env lean Hodge/Utils/DependencyCheck.lean` to verify
the proof track only depends on standard Lean axioms:
- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice)
- `Quot.sound` (quotient soundness)
-/

#print axioms hodge_conjecture_data
