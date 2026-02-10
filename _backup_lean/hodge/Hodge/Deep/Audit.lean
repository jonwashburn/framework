/-
Copyright (c) 2026 Hodge Formalization Project. All rights reserved.
Released under Apache 2.0 license.
Authors: Deep Track Formalization
-/
import Hodge.Deep

/-!
# Deep Track Audit

This module performs compile-time checks on the deep track formalization.

## Current State

When this file compiles, it reports the axiom dependencies of the `.real` instances.
Once all `sorry` goals are proved, the `.real` instances should have the same
kernel-axiom dependencies as the stub `.universal` instances (only `propext`, `Classical.choice`,
`Quot.sound`).

## Usage

```bash
lake build Hodge.Deep.Audit
```

## Completion Criteria

The deep track is COMPLETE when:
1. All `#print axioms` below show only `[propext, Classical.choice, Quot.sound]`
2. No `sorryAx` appears in any dependency
3. The `.real` instances can replace the `.universal` instances
-/

open Lean Meta Elab Command

-- ═══════════════════════════════════════════════════════════════════════════
-- AXIOM AUDIT: Deep Track Instances
-- ═══════════════════════════════════════════════════════════════════════════

-- These will show `sorryAx` until the deep track is complete.

-- Stokes/integration infrastructure now lives in the data-based layer:
-- `OrientedRectifiableSetData` / `ClosedSubmanifoldData` in `Hodge/Analytic/Currents.lean`.
-- The legacy `SubmanifoldIntegration` class is now a thin wrapper over explicit
-- `SubmanifoldIntegrationData` (no `.real` instance is maintained).
#print axioms Hodge.Deep.Stokes.hausdorffIntegrate_linear'
#print axioms Hodge.Deep.Stokes.hausdorffIntegrate_bound'
#print axioms Hodge.Deep.GAGA.ChowGAGAData.real
#print axioms Hodge.Deep.Microstructure.AutomaticSYRData.real'
#print axioms Hodge.Deep.HarveyLawson.HarveyLawsonKingData.real
#print axioms Hodge.Deep.FedererFleming.FlatLimitCycleData.real'
-- PD / fundamental class / spine bridge is currently represented by the explicit data-first interface
-- `SpineBridgeData_data` (see `Hodge/Classical/GAGA.lean`), re-exported in the deep pillar:
#print axioms Hodge.Deep.PoincareDuality.cycleClass_geom_eq_representingForm_data

-- ═══════════════════════════════════════════════════════════════════════════
-- SORRY COUNT: Deep Track Pillars
-- ═══════════════════════════════════════════════════════════════════════════

/-!
## Current Sorry Count

Run `./scripts/audit_stubs.sh --deep` to get a full sorry count for the deep track.

Or use grep:
```bash
grep -r "sorry" Hodge/Deep/Pillars/ | grep -v "\.olean" | grep -v "Status" | wc -l
```

### Target: 0 sorries

When all pillars are complete:
- `SubmanifoldIntegrationData` should be realized concretely (no legacy universal/real instances)
- `ChowGAGAData.real` can replace `ChowGAGAData.universal`
- etc.

Then the proof becomes **mathematically complete**, not just kernel-clean.
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- COMPLETION GATE (Uncomment when ready)
-- ═══════════════════════════════════════════════════════════════════════════

/-
-- When the deep track is complete, uncomment this to enforce no sorries:

elab "#guard_no_sorryAx " declName:ident : command => do
  let name := declName.getId
  let env ← getEnv
  let axiomsUsed := Lean.collectAxioms env name
  if axiomsUsed.contains `sorryAx then
    throwError m!"❌ DEEP AUDIT FAILURE: {name} still contains sorryAx"
  else
    logInfo m!"✅ {name} is sorry-free"

#guard_no_sorryAx Hodge.Deep.Stokes.SubmanifoldIntegration.real
#guard_no_sorryAx Hodge.Deep.GAGA.ChowGAGAData.real
-- ... etc
-/
