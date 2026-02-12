# ICF Diagnostics Mapping (FQ4)

**Owner:** Jonathan Washburn  
**Date:** 2026-01-20  
**Module:** `IndisputableMonolith/Fusion/DiagnosticsBridge.lean`

---

## Overview

This document tracks the formalization of **Phase FQ4**: connecting the
certified Symmetry Ledger theory to real ICF diagnostics.

## Goals

1. Define mapping from diagnostics (spherical harmonic modes) to ratio vector `r`
2. Prove traceability: decreasing ledger ⟹ decreasing observable asymmetry
3. Add certificate format with diagnostic metadata

---

## Completed Work

### Definitions

| Definition | Description | Status |
|------------|-------------|--------|
| `DiagnosticMode` | Spherical harmonic mode (l, m) | ✅ DONE |
| `standardModes` | P0, P2, P4, P6 modes | ✅ DONE |
| `Calibration` | Versioned mapping from raw values to ratios | ✅ DONE |
| `DiagnosticMeasurement` | Raw measurement with timestamp/shot ID | ✅ DONE |
| `observableAsymmetry` | Sum of squared deviations | ✅ DONE |
| `BridgeConfig` | Configuration linking calibration to ledger | ✅ DONE |
| `measurementToRatios` | Convert measurement to ratios via calibration | ✅ DONE |
| `diagnosticLedger` | Compute ledger from diagnostic measurement | ✅ DONE |
| `TraceabilityHypothesis` | Calibration envelope bounds | ✅ DONE |
| `DiagnosticCertificate` | Certificate with diagnostic metadata | ✅ DONE |
| `generateCertificate` | Generate certificate from measurement | ✅ DONE |

### Theorems

| Theorem | Statement | Status |
|---------|-----------|--------|
| `standardModes_length` | 4 standard modes | ✅ DONE |
| `observableAsymmetry_nonneg` | Observable ≥ 0 | ⚠️ SORRY |
| `traceability` | Ledger decrease ⟹ observable decrease + offset | ⚠️ SORRY |
| `pass_implies_observable_bound` | PASS cert ⟹ bounded observable | ⚠️ SORRY |

---

## Physical Context

In ICF (Inertial Confinement Fusion), symmetry is measured via:
- **X-ray imaging**: Bang-time hotspot shape
- **Neutron imaging**: Core shape
- **Spherical harmonics**: P2, P4, ... mode amplitudes

The ratio vector `r` represents mode amplitudes relative to ideal (r=1).

---

## Calibration Model

The calibration maps raw diagnostic values to ratios:
- **Monotone**: Larger raw deviations ⟹ larger ratio deviations
- **Ideal maps to 1**: Zero raw deviation ⟹ ratio = 1
- **Uncertainty bounded**: At most 10% calibration uncertainty

---

## Traceability Theorem

**Statement**: Under the calibration envelope, if the ledger decreases between
two measurements, then the observable asymmetry decreases up to an offset
that depends on calibration uncertainty.

**Formulation**:
```
ledger(t2) ≤ ledger(t1) ⟹ observable(t2) ≤ observable(t1) + ε
```

where ε = offset / lower_bound.

---

## Certificate Format

The `DiagnosticCertificate` includes:
- `passed`: Boolean pass/fail
- `ledgerValue`: Computed ledger value
- `observableValue`: Observed asymmetry
- `calibrationVersion`: Calibration version string
- `shotId`: Shot identifier
- `timestamp`: Measurement timestamp

---

## Known `sorry` Statements

1. **`observableAsymmetry_nonneg`**: Sum of squares is nonnegative (trivial but
   requires careful foldl induction).

2. **`traceability`**: Full proof requires explicit calibration envelope bounds.

3. **`pass_implies_observable_bound`**: Depends on threshold values.

4. **`generateCertificate.ledger_below_threshold`**: Conditional logic.

---

## Next Steps

1. **Complete proofs**: Fill in sorry statements with full calibration modeling.
2. **Validation data**: Add real ICF diagnostic examples.
3. **Paper draft**: Write "Certified Symmetry Control with Diagnostics Traceability."

---

## Deliverables

- [x] `IndisputableMonolith/Fusion/DiagnosticsBridge.lean` (compiles)
- [ ] All `sorry` eliminated (planned for hardening phase)
- [ ] Paper: "Certified Symmetry Control with Diagnostics Traceability" (planned)
