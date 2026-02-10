## Collaboration Proposal: RS Coherence-Controlled Drive Profiles in Full Rad-Hydro

### Executive Summary

We have implemented a **seam-first, auditable** control-layer prototype for applying Recognition Science (RS) coherence metrics to fusion driver timing and symmetry optimization. A proxy-model study indicates large potential leverage under assumed coherence improvements. To move from proxy sensitivity to **physics validation**, we propose a collaboration with a rad-hydro team to run **full radiation-hydrodynamics simulations** (HYDRA / DRACO / LASNEX) using RS-generated drive profiles and symmetry objectives.

### What We Have Today (Implemented + Auditable)

- **Pulse scheduling (φ-structured timing)**:
  - Generator: `fusion/simulator/fusion/pulse_scheduler.py`
  - Window-gated scheduler (control systems): `fusion/simulator/control/phi_window_scheduler.py`
- **Coherence metrics**:
  - Temporal coherence \(C_\varphi\): `fusion/simulator/coherence/phi_coherence.py`
  - Symmetry/ledger sync \(C_\sigma\): `fusion/simulator/coherence/ledger_sync.py`
- **Barrier-scale proxy computation**:
  - \(S = 1/(1 + C_\varphi + C_\sigma)\), \(G_\mathrm{eff}=1/S^2\)
  - Implementation: `fusion/simulator/coherence/barrier_scale.py`
- **Rad-hydro integration artifact export (new)**:
  - Canonical `time_ns power_TW` table export + metadata: `fusion/simulator/radhydro/hydra_pulse_export.py`
  - This intentionally avoids assuming facility-specific deck syntax.
- **Formal artifacts (Lean)**:
  - Definitions + monotone bounds: `IndisputableMonolith/Fusion/ReactionNetworkRates.lean`
  - Screening inequality: `IndisputableMonolith/Fusion/BarrierScreening.lean`

### What We Need From the Rad-Hydro Team

- Access to a **baseline deck** and its tuning notes (NIF-class ICF or other facility).
- Agreement on a **simulation campaign** (small matrix first), and which diagnostics are authoritative.
- A mechanism to ingest **tabulated time-power profiles** (we provide the table; you integrate into the deck).

### Proposed Work Plan

#### Phase 0 — Baseline Lock

- Confirm baseline deck reproduces reference metrics (yield, symmetry, bang time, etc.).
- Freeze baseline parameters for A/B comparisons.

#### Phase 1 — RS Timing A/B

- Case A: baseline pulse
- Case B: RS φ-structured pulse train with **equal total energy**
  - Generated via `fusion/simulator/radhydro/hydra_pulse_export.py`
- Deliverable: first-pass comparison of yield + symmetry + stability metrics.

#### Phase 2 — RS Timing + Symmetry Objective (Optional)

- If your workflow supports beam-balance/symmetry tuning, add a control objective aligned with the RS ledger:
  - Use mode amplitudes (P2/P4 or equivalent) as the observable basis.
  - Map to ledger ratios and compute \(C_\sigma\) (calibration seam, explicitly logged).

#### Phase 3 — Calibration Envelope + Robustness Sweeps

- Small parameter sweeps over:
  - pulse count, sigma/width, total duration
  - perturbations (target offsets, drive asymmetry, timing jitter) to test robustness

### Success Criteria (What Counts as “Works”)

Minimum:
- RS pulse variants do **not** degrade baseline outcomes under equal energy and consistent physics models.

Positive evidence:
- Improved symmetry metrics (lower P2/P4), reduced RT growth, improved yield or burn robustness.
- Measured observables correlate with RS metrics \((C_\varphi, C_\sigma)\) in the expected direction.

### Deliverables

- A table of runs (deck hash / revision, input pulse table hash, outputs).
- Extracted diagnostics time series and summary KPIs.
- A documented mapping from rad-hydro outputs → \(C_\varphi, C_\sigma\) (calibration envelope).
- Recommendations: which φ structures are stable vs which introduce hydro pathologies.

### Operations / Data Handling

- We can work either:
  - **On-site / secure environment** (preferred for HYDRA-class workflows), or
  - With a limited dataset of **non-sensitive** outputs and a deck surrogate, depending on constraints.

### Next Step (Fast Start)

- Identify one baseline deck and one reference shot/design.
- Run the protocol in `fusion/planning/HYDRA_VALIDATION_PROTOCOL.md` for a first A/B.
- Share the first comparison results and decide whether to expand into a sweep.

