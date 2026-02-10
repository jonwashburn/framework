## RS Fusion: Rad-Hydro Validation Protocol (HYDRA / DRACO / LASNEX)

### Scope / Claim Boundary (Seam-First)

- **This protocol validates** whether RS-style **φ-structured timing** and **symmetry-ledger control objectives** improve outcomes in a **full radiative hydrodynamics simulation**.
- **This protocol does not claim** that the proxy-model yield multiplier (~8.5×) is physically realized until confirmed in rad-hydro.
- **Math is proven; physics is a seam**:
  - The code can provably compute \(S = 1/(1 + C_\varphi + C_\sigma)\) and derived quantities.
  - Whether \(S\) corresponds to real Coulomb barrier screening in a facility is what rad-hydro validation is for.

### Required Inputs (from the rad-hydro team)

- **A baseline deck** (NIF-class or facility-specific) that currently reproduces a known shot or reference design:
  - Laser energy (MJ), pulse length (ns), spot/CBET model choices, hohlraum/target geometry, materials, EOS/opacities.
  - Any existing tuning parameters used to match data (keep unchanged across variants unless explicitly swept).
- **Clear definition of “success metrics”** for the chosen baseline (yield, bang time, symmetry, burn width, etc.).

### RS Artifacts We Provide (from this repo)

- **Pulse table generator (canonical time-power table)**:
  - `fusion/simulator/radhydro/hydra_pulse_export.py`
  - Produces a two-column table: `time_ns power_TW` + JSON metadata header.
  - Intended to be ingested into HYDRA/DRACO/LASNEX using your local deck conventions.
- **Coherence + barrier proxy implementation**:
  - `fusion/simulator/coherence/phi_coherence.py` (computes \(C_\varphi\) from timing/phase errors)
  - `fusion/simulator/coherence/ledger_sync.py` (computes \(C_\sigma\) from symmetry/mode ratios via J-ledger)
  - `fusion/simulator/coherence/barrier_scale.py` (computes \(S\), \(1/S^2\), \(\eta_\mathrm{RS}\))
- **Formal references (Lean)**:
  - `IndisputableMonolith/Fusion/ReactionNetworkRates.lean` (definitions + monotone bounds)
  - `IndisputableMonolith/Fusion/BarrierScreening.lean` (screening inequality; *physics identification remains a seam*)

### Experiment Design

#### Case A: Baseline

- Run the baseline deck unchanged.
- Record all diagnostics listed below.

#### Case B: RS Timing Variant (φ pulse structure)

- Keep **total laser energy identical** to baseline.
- Replace the baseline time-dependent drive with an RS-exported profile:
  - Generate a φ-interval sub-pulse train with a duration comparable to the baseline pulse length.
  - Use the export tool to match energy.

Suggested starting point (NIF-like):

```bash
python -m fusion.simulator.radhydro.hydra_pulse_export \
  --output fusion/out/hydra_phi_pulse_table.dat \
  --n-pulses 8 \
  --total-duration-ns 20 \
  --pulse-sigma-ns 1.0 \
  --dt-ns 0.02 \
  --energy-MJ 1.8
```

**Integration seam:** the rad-hydro team maps `hydra_phi_pulse_table.dat` into the deck’s laser drive definition.

#### Case C: RS Timing + Symmetry-Control Variant (optional)

- Same as Case B, plus:
  - Use your existing symmetry knobs (beam balance, pointing, P2/P4 tuning, etc.)
  - Optimize toward a *symmetry objective* that the RS ledger can measure.

This case is about determining whether **achievable symmetry improvements** correlate with improved outcomes, and how to map sim outputs into \(C_\sigma\).

### Parameter Sweep (Minimal but Informative)

Run a small matrix to avoid “one-off” conclusions:

- **n_pulses**: {6, 8, 10}
- **pulse_sigma_ns**: {0.03, 0.05, 0.08}
- **total_duration_ns**: {baseline_length, ±20%}
- **(optional)** add “baseline envelope” weighting (foot vs main) once a baseline ingestion path works

### Diagnostics to Extract (per run)

At minimum:

- **Yield** (MJ), burn-weighted ion temperature, burn width, bang time
- **Hot-spot metrics**: \(T_i\), \(P\), \(\rho R\), areal density evolution
- **Symmetry / modes**:
  - P2/P4 (Legendre) or low-mode spherical harmonics over time
  - Time history of mode amplitudes at key surfaces (ablation front, fuel/hotspot boundary)
- **Instability proxies**:
  - RT growth factors (ablator/fuel interfaces)
  - Mix metrics (if tracked)
- **Drive history**:
  - Laser power vs time at input
  - Absorbed power (CBET/LPI losses if modeled)
  - Radiation temperature (hohlraum) vs time if applicable

### How We Compute RS Metrics from Rad-Hydro Outputs

#### \(C_\varphi\) (temporal coherence)

Inputs (examples):
- Commanded pulse centers from export metadata (`centers_ns`)
- Measured/realized “effective” pulse timing from rad-hydro (e.g., absorbed power peaks, shock timing markers)

Compute:
- Jitter RMS and skew RMS (facility-specific extraction seam)
- Apply the RS mapping in `fusion/simulator/coherence/phi_coherence.py`

#### \(C_\sigma\) (symmetry / ledger sync)

Inputs:
- Low-mode amplitudes (P2/P4 or equivalent) or ratios derived from them

Compute:
- Convert raw mode amplitudes into ratios \(r_i \approx 1 + g_i \cdot a_i\) (calibration seam)
- Run `fusion/simulator/coherence/ledger_sync.py` to compute ledger value \(L\) and \(C_\sigma = 1/(1 + L/\Lambda)\)

### Evaluation / Acceptance Criteria

Minimum acceptance:
- **No degradation** of baseline (yield, symmetry, instability metrics) when switching to RS profile under equal energy.

Positive evidence:
- Improved symmetry metrics (lower P2/P4) and/or reduced instability growth
- Improved yield or more robust burn (lower sensitivity to perturbations)
- Correlation: higher computed \((C_\varphi, C_\sigma)\) aligns with improved outcomes

### Deliverables (to close the loop)

- Table of runs + metrics (A/B/C + sweep)
- A mapping from rad-hydro observables → \(C_\varphi, C_\sigma\) calibration envelope (even if coarse)
- A summary of which RS timing structures are stable vs which trigger hydro pathologies

