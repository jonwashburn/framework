# Calibration Seam Policy

## Overview

Recognition Science maintains a **strict separation** between:

1. **Cost-First Core**: Derivations from RCL → J = Jcost → φ → predictions
2. **External Anchors**: CODATA/empirical values for validation

This document defines the policy and provides audit instructions.

## Architectural Separation

### Cost-First Core (No External Dependencies)

These modules contain **zero** external calibration data:

| Module | Purpose |
|--------|---------|
| `IndisputableMonolith/Cost.lean` | J-cost derivation from RCL |
| `IndisputableMonolith/Constants.lean` | RS-native units (τ₀, ℓ₀, c=1) |
| `IndisputableMonolith/Foundation/*.lean` | Forcing chain (T0-T8) |

The core derives all predictions from the single primitive (RCL).

### External Anchor Modules (CODATA/Empirical)

These modules contain **explicit calibration data**:

| Module | Purpose |
|--------|---------|
| `Constants/ExternalAnchors.lean` | CODATA 2022 values (c, ℏ, G, α, masses) |
| `Constants/Codata.lean` | Legacy CODATA (quarantined) |
| `Verification/Exclusivity/Observables.lean` | Empirical bounds for validation |

All definitions in these modules are marked with `**EXTERNAL ANCHOR**` in docstrings.

## Mechanical Labeling

### Docstring Convention

All external anchor definitions include the tag:

```
**EXTERNAL ANCHOR**
```

This enables mechanical auditing:

```bash
# Count all external anchors
grep -r "EXTERNAL ANCHOR" IndisputableMonolith --include="*.lean" | wc -l

# List all external anchor locations
grep -rn "EXTERNAL ANCHOR" IndisputableMonolith --include="*.lean"

# Verify cost-first core is clean
grep -l "ExternalAnchors" IndisputableMonolith/Cost.lean \
  IndisputableMonolith/Constants.lean \
  IndisputableMonolith/Foundation/*.lean
# Should return no results
```

### Naming Conventions

External anchor definitions use specific suffixes:

- `_SI`: SI-unit values (e.g., `c_SI`, `hbar_SI`)
- `_CODATA`: CODATA central values (e.g., `alpha_inv_CODATA`)
- `_uncertainty`: Measurement uncertainties (e.g., `alpha_inv_CODATA_uncertainty`)

## Import Policy

### Rule 1: Cost-First Core Must Not Import External Anchors

```lean
-- FORBIDDEN in Cost.lean, Constants.lean, Foundation/*.lean:
import IndisputableMonolith.Constants.ExternalAnchors
import IndisputableMonolith.Constants.Codata
```

### Rule 2: Validation Modules May Import External Anchors

```lean
-- ALLOWED in Verification/*.lean, Experimental/*.lean:
import IndisputableMonolith.Constants.ExternalAnchors
```

### Rule 3: Comparison Theorems Must Be Marked

When a theorem bridges cost-first predictions to external bounds:

```lean
/-- **CALIBRATION SEAM**: This theorem bridges:
    - Cost-first derived values (rsObservables)
    - External empirical bounds (CODATA 2022) -/
theorem rs_within_bounds : withinBounds rsObservables := ...
```

## Current Statistics

As of 2026-01-03:

- **External Anchor markers**: 45
- **Core modules (clean)**: Cost.lean, Constants.lean, Foundation/
- **Anchor modules**: ExternalAnchors.lean, Observables.lean

## Audit Checklist

- [ ] Run: `grep -l "ExternalAnchors" IndisputableMonolith/Cost.lean` → no results
- [ ] Run: `grep -l "ExternalAnchors" IndisputableMonolith/Constants.lean` → no results
- [ ] Run: `grep -l "CODATA" IndisputableMonolith/Cost.lean` → no results
- [ ] Run: `grep -r "EXTERNAL ANCHOR"` → all marked appropriately
- [ ] Review: `ExternalAnchors.lean` contains only CODATA values
- [ ] Review: `Observables.lean` separates derived predictions from bounds

## Rationale

This separation ensures:

1. **Falsifiability**: RS predictions are fixed before comparison to data
2. **No Circular Calibration**: Predictions don't depend on what they predict
3. **Auditability**: Any external data is mechanically identifiable
4. **Modularity**: Updating CODATA values doesn't touch the cost-first core

