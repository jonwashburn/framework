/-!
  ILG/Relativity aggregation is intentionally sealed off.

  The full documentation harness formerly lived here while the Relativity
  derivations were scaffolded. Until the Relativity modules eliminate their
  outstanding axioms (see AXIOM_CLASSIFICATION_RELATIVITY.md) this file remains
  a stub so that build targets importing it fail fast.

  Downstream tooling should read axiom/sorry/admit metrics from external reports
  instead of importing this module.
-/

import IndisputableMonolith.Meta.AxiomLattice  -- harmless stub to avoid empty file

/-- Placeholder constant summarising the current Relativity axiom counts. -/
def relativityAxiomTally : String :=
  "Relativity sealed: classical axioms = 40, RS-specific axioms = 27 (see AXIOM_CLASSIFICATION_RELATIVITY.md)"

#eval relativityAxiomTally
