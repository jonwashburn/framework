# ICF Pipeline Hardening Plan (Audit Spine + Mode Extraction + Proof Bridge)

**Owner:** Jonathan Washburn  
**Scope:** Hardening the *diagnostic → modes → ledger → certificates → control* stack for national-lab-grade audit, starting from public datasets and paper-digitized modes, and converging toward facility diagnostics.

This plan is written to avoid “busywork”: every task either (a) reduces the empirical seam, (b) increases auditability, or (c) improves robustness/validity of symmetry modes and \(C_\sigma\).

**Status:** Implemented in repo (2026-01-25).  
**Replay:** `python -m rs_fusion_simulator.selfcheck` and `lake build IndisputableMonolith.Fusion.DiagnosticsBridge`.

---

## North Star

Produce a pipeline where every run emits a **single auditable artifact** containing:

- provenance (data source, DOI/paper, file hashes),
- all seam parameters (axis, threshold, edge method, calibration),
- computed modes \(P_2/P_0, P_4/P_0\),
- the **Lean-aligned** symmetry ledger + \(C_\sigma\),
- uncertainty bounds (explicitly marked as seam modeling),
- and (optionally) a control recommendation with justification.

And in Lean:

- isolate the only remaining seam as a **calibration envelope assumption** (explicit predicate),
- eliminate trivial `sorry` statements that do not require physics.

---

## Current Baseline (What Exists Now)

### Python
- `rs_fusion_simulator/control/icf_modes.py`
  - image-based boundary ray-cast + Legendre fit → \(P_2/P_0, P_4/P_0\) (**seam**).
- `rs_fusion_simulator/control/jag_dataset.py`
  - loads JAG `.npy` bundle (inputs/scalars/images).
- `rs_fusion_simulator/control/jag_demo.py`
  - computes \(C_\sigma\) from:
    - anisotropy proxy, or
    - image-based \(P_2/P_0,P_4/P_0\), or
    - dataset-provided scalar columns.
- `rs_fusion_simulator/control/paper_modes_demo.py`
  - CSV ingest of paper-digitized \(P_2/P_0,P_4/P_0\).

### Lean
- `IndisputableMonolith/Fusion/DiagnosticsBridge.lean` (FQ4 bridge)
- `IndisputableMonolith/Fusion/SymmetryLedger.lean` (ledger theory)

---

## Milestones (Ordered by ROI)

### M1 — Audit Spine: Seam-first run artifacts (**must-have**)
**Deliverables**
- A JSON artifact schema + generator:
  - data source fields (DOI/paper),
  - file SHA-256 hashes,
  - extraction params (axis, thresholds, edge method),
  - calibration mode + parameters,
  - explicit “certified vs seam” flags.
- `jag_demo` and `paper_modes_demo` write artifacts to an output directory.

**Acceptance**
- Re-running with identical inputs produces identical `input_hash` and file hashes.
- Artifact always includes a “seams” list and a “certified_surface” list.

**Implemented**
- Artifact schema + helpers: `rs_fusion_simulator/control/artifacts.py`
- JAG artifact emission: `rs_fusion_simulator/control/jag_demo.py` (`--out-dir`)
- Paper CSV artifact emission: `rs_fusion_simulator/control/paper_modes_demo.py` (`--out-dir`)

### M2 — Always-positive calibration option: \(r=\exp(g\cdot m)\)
**Deliverables**
- Optional calibration mode that guarantees ratios \(>0\).
- Artifact records calibration mode and parameters.

**Acceptance**
- No ratio negativity edge-cases; logs which mapping was used.

**Implemented**
- `--calibration exp` (and `--calibration affine`) in:
  - `rs_fusion_simulator/control/jag_demo.py`
  - `rs_fusion_simulator/control/paper_modes_demo.py`

### M3 — Axis rigor: auto-axis selection + confidence
**Deliverables**
- Auto-axis estimator (grid search / moment-based) returning:
  - selected axis angle,
  - confidence metric (separation between best and runner-up).
- Artifact records chosen axis and confidence.

**Acceptance**
- Axis choice is reproducible and logged.

**Implemented**
- Auto-axis search: `rs_fusion_simulator/control/icf_modes.py` (`auto_axis_fit_legendre_p2_p4_from_profile`)
- CLI: `rs_fusion_simulator/control/jag_demo.py` (`--auto-axis`, `--axis-grid-step-deg`)
- Stored in artifacts as `axis_angle_deg` + `axis_confidence`.

### M4 — Uncertainty quantification + ledger bounds
**Deliverables**
- Bootstrap/noise perturbation option for \(P_2/P_0,P_4/P_0\).
- Propagate to ledger distribution (min/max/quantiles), explicitly marked as seam.

**Acceptance**
- Artifact includes uncertainty fields and method parameters.

**Implemented**
- Bootstrap + optional radii noise: `rs_fusion_simulator/control/icf_modes.py` (`bootstrap_legendre_p2_p4_from_profile`)
- CLI: `rs_fusion_simulator/control/jag_demo.py` (`--uncertainty-bootstrap`, `--uncertainty-noise-sigma-px`, `--uncertainty-seed`)
- Propagates to ledger/ledger_sync distributions and stores summaries in artifacts.

### M5 — Robust edge extraction (reduce sensitivity)
**Deliverables**
- Preprocessing options (background subtraction, smoothing).
- Edge method option: threshold-crossing vs max-gradient.
- Artifact records method and parameters.

**Acceptance**
- Output stability improves on brightness/contrast variations (synthetic regression tests).

**Implemented**
- Preprocessing + edge options: `rs_fusion_simulator/control/icf_modes.py`
  - background subtraction (`background_percentile`)
  - smoothing (`blur_sigma`)
  - edge method (`threshold` vs `max_grad`)
- CLI wiring: `rs_fusion_simulator/control/jag_demo.py` (`--edge-method`, `--background-percentile`, `--blur-sigma`)

### M6 — True mode ingestion adapters (no image seam when available)
**Deliverables**
- Standard adapter interface for “facility provides \(P_2/P_0,P_4/P_0\)” with provenance.

**Acceptance**
- Same artifact format works whether modes come from images or direct mode outputs.

**Implemented**
- JAG: `--mode-source scalars_p2p4` reads dataset-provided columns.
- Artifact format is identical (only `mode_source` changes).

### M7 — Paper-digitization rigor: provenance + receipt
**Deliverables**
- Provenance required/optional fields (DOI, figure id, digitizer/tool, mapping notes).
- Emit a “digitization receipt” JSON including CSV file hash + timestamp.

**Acceptance**
- Receipt + artifacts provide chain-of-custody for paper-derived data.

**Implemented**
- `rs_fusion_simulator/control/paper_modes_demo.py`:
  - `--require-provenance`
  - `--receipt-out` (CSV hash + timestamp receipt)

### M8 — Control suggestions (seam model, but useful)
**Deliverables**
- Minimal symmetry-trim controller using facility-supplied sensitivity/Jacobian matrix.
- Outputs a recommended trim vector and predicted mode reduction.

**Acceptance**
- Output is deterministic given the supplied model and logged as seam.

**Implemented**
- Controller: `rs_fusion_simulator/control/symmetry_controller.py`
- Demo CLI: `python -m rs_fusion_simulator.control.symmetry_controller_demo --help`

### M9 — Lean hardening: remove trivial `sorry`
**Deliverables**
- In `Fusion/DiagnosticsBridge.lean` and `Fusion/SymmetryLedger.lean`:
  - remove trivial sorries,
  - restructure hypotheses so only the calibration envelope remains a seam.

**Acceptance**
- `lake build IndisputableMonolith.Fusion.DiagnosticsBridge` succeeds with fewer/no sorries (except explicitly labeled seam assumptions).

**Implemented**
- `IndisputableMonolith/Fusion/DiagnosticsBridge.lean` now compiles with **no `sorry`**.
- Remaining seam is explicit as `TraceabilityHypothesis.observable_le`.

### M10 — Certified interface for calibration envelope (Lean ↔ Python)
**Deliverables**
- Lean predicate describing calibration envelope assumptions, matching what artifacts record.
- Python artifact schema references the predicate by theorem name.

**Implemented**
- Lean seam predicate: `IndisputableMonolith.Fusion.DiagnosticsBridge.TraceabilityHypothesis.observable_le`
- Referenced in artifacts (Python):
  - `rs_fusion_simulator/control/jag_demo.py`
  - `rs_fusion_simulator/control/paper_modes_demo.py`
  - `rs_fusion_simulator/control/image_folder_demo.py`

### M11 — No import-time side effects: explicit selfcheck + tests
**Deliverables**
- Remove “print on import” and “verify on import” across the simulator.
- Add `python -m rs_fusion_simulator.selfcheck`.
- Add a minimal pytest suite for core invariants.

**Implemented**
- Selfcheck entrypoint: `rs_fusion_simulator/selfcheck.py`
  - Run: `python -m rs_fusion_simulator.selfcheck`
- Test gate (dependency-free): `rs_fusion_simulator/tests/test_selfcheck.py`
  - Run: `python -m unittest discover -s rs_fusion_simulator/tests -p "test_*.py" -q`
- (Optional) pytest: repository includes a pytest-style test as well (when pytest is installed).

### M12 — Public dataset expansion beyond JAG
**Deliverables**
- Generic image-folder dataset adapter + metadata JSON.
- Document 1–2 candidate public HEDP datasets and how to ingest them.

**Implemented**
- Generic adapter: `rs_fusion_simulator/control/image_folder_dataset.py`
- Demo: `rs_fusion_simulator/control/image_folder_demo.py`
- Public-source notes: `planning/ICF_PUBLIC_DATA_SOURCES.md`

---

## Execution Notes

- **Seam honesty is non-negotiable**: anything not kernel-checked must be explicitly labeled “seam” in artifacts.
- **Keep Lean builds incremental**:
  - `lake build IndisputableMonolith.Fusion.DiagnosticsBridge`
  - `lake build IndisputableMonolith.Fusion.SymmetryLedger`

---

## Replay Commands (after each milestone)

```bash
# Python
python -m rs_fusion_simulator.control.jag_demo --help
python -m rs_fusion_simulator.control.paper_modes_demo --help

# Lean (incremental)
lake build IndisputableMonolith.Fusion.DiagnosticsBridge
lake build IndisputableMonolith.Fusion.SymmetryLedger
```

