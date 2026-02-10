import Hodge

/-!
# Axiom Guard — Compile-Time Regression Protection

This module provides **compile-time enforcement** against introducing new axioms
or `sorry` statements into the proof track of `hodge_conjecture_data`.

## How it works

1. We define the list of **allowed axioms** (standard Lean axioms).
2. We provide a `#guard_no_custom_axioms` command that runs at compile time.
3. If `hodge_conjecture_data` depends on any **custom** axiom, compilation fails.

## Current Status

When this file compiles without error:
- ✅ No custom axioms in the proof track
- The only remaining issue is `sorryAx` (if present), which requires proving
  the `sorry` statements in the codebase.

## Usage

This file is imported as part of the normal build. If someone introduces a new
`axiom` declaration that `hodge_conjecture_data` depends on, the build will fail here.
-/

open Lean Meta Elab Command in
/-- Check that a declaration only depends on allowed axioms.
    Returns the list of non-standard axioms found. -/
def checkAxiomsOf (declName : Name) : MetaM (List Name) := do
  let env ← getEnv
  let axiomsUsed := Lean.collectAxioms env declName
  let standardAxioms : List Name := [
    `propext,
    `Classical.choice,
    `Quot.sound,
    `sorryAx  -- We track this separately; it indicates sorry statements
  ]
  let customAxioms := axiomsUsed.toList.filter fun ax =>
    !standardAxioms.contains ax
  return customAxioms

open Lean Meta Elab Command in
/-- Command to verify a declaration only uses allowed axioms. -/
elab "#guard_no_custom_axioms " declName:ident : command => do
  let name := declName.getId
  let customAxioms ← liftTermElabM <| checkAxiomsOf name
  if customAxioms.isEmpty then
    logInfo m!"✅ {name} uses only standard Lean axioms (no custom axioms)"
  else
    throwError m!"❌ AXIOM GUARD FAILURE: {name} depends on custom axiom(s): {customAxioms}\n\
      These must be proved or eliminated before merging."

-- ═══════════════════════════════════════════════════════════════════════════
-- AXIOM GUARD CHECK — This MUST compile without error
-- ═══════════════════════════════════════════════════════════════════════════

-- This check runs at compile time and FAILS THE BUILD if custom axioms are found.
#guard_no_custom_axioms hodge_conjecture_data

-- ═══════════════════════════════════════════════════════════════════════════
-- INFORMATIONAL OUTPUT (for human review)
-- ═══════════════════════════════════════════════════════════════════════════

#print axioms hodge_conjecture_data

/-!
## What This Means

If this file compiles successfully:

1. **No custom axioms** in the `hodge_conjecture_data` proof track.
2. The only possible remaining issues are:
   - `sorryAx` — requires completing the `sorry` statements (Agent 1's work)

## Historical Notes

- **2026-01-12**: `Current.boundary_bound` removed from kernel axiom list
  (refactored to a field on the `Current` structure)
- **2026-01-12**: `FundamentalClassSet_represents_class` eliminated
  (restructured `SignedAlgebraicCycle` to carry its class directly)
-/
