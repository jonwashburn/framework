# RS / Fusion IP Inventory + Protection Strategy (Working Draft)

**Owner:** Jonathan Washburn (Recognition Science Institute)  
**Date:** 2026-01-25  
**Scope:** Innovations implemented and/or formalized in this repo, with emphasis on the **fusion control + audit + certification** stack.

**Not legal advice.** This is an engineering-first inventory to hand to patent counsel so they can draft filings efficiently.

---

## Principle: Separate “law of nature” from “protectable engineering”

- **Not directly patentable** (as a category): broad scientific claims (“the universe works this way”), bare math, and abstract ideas.
- **Often patentable** when framed as a concrete system/method: specific **control pipelines**, **diagnostic transforms**, **certificate/audit mechanisms**, **hardware-software interfaces**, deterministic algorithms with measurable improvements (robustness, auditability, reproducibility), and implementation details.

In our repo, the **protectable core** is the *RS-fusion control stack as an engineered method*:

> diagnostics → ratios/modes → symmetry ledger → coherence metrics → barrier scaling → actionable control recommendation → auditable certificate bundle

---

## IP “Families” (group inventions into filings)

Think of each family below as a candidate **provisional** (then later non-provisional) with multiple claim types:
- **method claims** (steps)
- **system claims** (modules + interfaces)
- **computer program product claims**

### Family A — Coherence-controlled barrier scaling for fusion (S, Teff, temperature scaling)

- **What it is**: A coherence-derived reduction of the effective tunneling barrier via
  - \(S = 1/(1 + C_\varphi + C_\sigma)\)
  - \(\eta_{\mathrm{RS}} = S \cdot \eta_{\mathrm{classical}}\)
  - effective-temperature identity in the proxy: \(T_{\mathrm{eff}} = T/S^2\)
- **Why it’s claimable**: This is not “a formula”; it’s a **control computation** that maps measurable coherence/symmetry observables into a new effective barrier term used to compute yields/thresholds/control decisions.
- **Evidence (Lean, model-layer)**:
  - `IndisputableMonolith/Fusion/ReactionNetworkRates.lean`
  - `IndisputableMonolith/Fusion/Ignition.lean` (effective-temperature identity + ignition transfer)
- **Evidence (Python)**:
  - `fusion/simulator/coherence/barrier_scale.py`
  - `fusion/simulator/fusion/shot_simulator.py`
- **Seams**:
  - calibration of how Cφ/Cσ relate to facility physics is empirical, but the computation and monotonicity guarantees are certified.

### Family B — Symmetry ledger + ledgerSync metric (J-cost objective as a control observable)

- **What it is**:
  - symmetry ledger \(L = \sum_m w_m \, J(r_m)\) with \(J(x) = (x + x^{-1})/2 - 1\)
  - `ledgerSync = 1/(1 + L/Λ)` as a bounded [0,1] actuator-friendly metric
- **Why it’s claimable**: A **specific**, symmetric, convex, audit-friendly cost + a deterministic transform into a bounded metric that can be used by controllers and logged/certified.
- **Evidence (Lean)**:
  - `IndisputableMonolith/Fusion/SymmetryLedger.lean`
  - `IndisputableMonolith/Cost.lean` (J properties underpinning the ledger)
- **Evidence (Python)**:
  - `fusion/simulator/foundations/jcost.py`
  - `fusion/simulator/coherence/ledger_sync.py`
  - `fusion/simulator/control/*_demo.py` (artifact emission)
- **Seams**:
  - choice of weights and thresholds is policy; still fully auditable.

### Family C — φ scheduling + eight-tick phase structure for pulsed drivers

- **What it is**:
  - pulse timing/scheduling constrained by φ-ratio windows
  - eight-tick phase assignments (kπ/4)
  - jitter robustness formalization (quadratic-vs-linear degradation model)
- **Why it’s claimable**: A concrete scheduling method for pulsed drivers with robustness properties and a deterministic mapping into control phases.
- **Evidence (Lean)**:
  - `IndisputableMonolith/Fusion/Scheduler.lean`
  - `IndisputableMonolith/Fusion/JitterRobustness.lean`
  - `IndisputableMonolith/Fusion/GeneralizedJitter.lean` (capsule conditions)
- **Evidence (Python)**:
  - `fusion/simulator/fusion/pulse_scheduler.py`
  - `fusion/simulator/foundations/eight_tick.py`
- **Seams**:
  - facility driver constraints (hardware timing resolution, channel coupling) are operational seams; the scheduling algorithm remains deterministic/auditable.

### Family D — Diagnostic-to-mode extraction (P2/P4) + robustness + uncertainty

- **What it is**:
  - extracting \(P_2/P_0, P_4/P_0\) from images via boundary sampling + Legendre fit
  - auto-axis estimation + confidence
  - robust edge detection options + bootstrap uncertainty
  - calibration mappings (affine + always-positive exp mapping)
- **Why it’s claimable**: A practical diagnostic-processing method that yields stable symmetry modes and emits a full audit trail of seam parameters.
- **Evidence (Python)**:
  - `fusion/simulator/control/icf_modes.py`
  - `fusion/simulator/control/jag_demo.py`
  - `fusion/simulator/control/paper_modes_demo.py`
  - `fusion/simulator/control/image_folder_demo.py`
- **Seams**:
  - any image-to-mode extraction is an empirical seam until validated against facility ground-truth mode outputs; we explicitly label this in artifacts.

### Family E — Audit spine / certificates / chain-of-custody artifacts (“seams-first”)

- **What it is**: Every run emits a deterministic artifact containing:
  - provenance, hashes, seam parameters, computed outputs, Lean theorem refs, and optional control actions
- **Why it’s claimable**: This is a deployment-grade compliance mechanism (reproducibility + nonrepudiation) for reactor control pipelines.
- **Evidence (Python)**:
  - `fusion/simulator/control/artifacts.py`
  - `fusion/simulator/fusion/certificate.py`
  - `fusion/simulator/selfcheck.py` (no import-time side effects)
- **Evidence (Lean)**:
  - `IndisputableMonolith/Fusion/Executable/Interfaces.lean` (certificate bundle interface)
- **Seams**:
  - the artifact explicitly lists what is seam vs certified; that “seam honesty” is itself part of the engineered system.

### Family F — Lean-certified diagnostics bridge (calibration envelope seam, explicitly isolated)

- **What it is**:
  - a typed model of diagnostics, calibration, observable asymmetry proxy
  - a formal theorem linking ledger decrease to bounded observable decrease **under a single explicit hypothesis**
- **Why it’s claimable**: The invention is the **architecture**: facility-supplied envelope + certified reasoning + certificate metadata binding.
- **Evidence (Lean)**:
  - `IndisputableMonolith/Fusion/DiagnosticsBridge.lean`
  - seam predicate: `TraceabilityHypothesis.observable_le`
- **Evidence (Python)**:
  - artifacts reference the Lean seam predicate in run outputs (`lean_predicate`)
- **Seams**:
  - facility must provide calibration envelope evidence; the seam is intentionally single-point and auditable.

### Family G — Formal viability/ignition certification (explicit L(T,…) + P(T,…) + thresholds)

- **What it is**:
  - commits to explicit (auditable) loss model + deposited heating proxy
  - proves sufficient conditions and explicit thresholds \(T^\*, E^\*\) for viability (model-layer)
- **Why it’s claimable**: A method for producing *auditable viability certificates* that are replayable and link directly to kernel-checked theorems.
- **Evidence (Lean)**:
  - `IndisputableMonolith/Fusion/PowerBalance.lean`
  - `IndisputableMonolith/Fusion/ReactivityProxy.lean`
  - `IndisputableMonolith/Fusion/PowerBalanceBounds.lean`
  - `IndisputableMonolith/Fusion/ViabilityThresholds.lean`
- **Evidence (Python, added during review)**:
  - `fusion/simulator/fusion/reactivity_proxy.py`
  - `fusion/simulator/fusion/power_balance.py`
  - `fusion/simulator/fusion/viability_thresholds.py`
- **Seams**:
  - coefficients/units are facility-specific; the *structure* and sufficiency proofs are certified.

### Family H — Nuclear pathway optimization via “magic distance” attractors + shell correction proxy

- **What it is**:
  - stability distance to magic numbers
  - reaction network scoring/attractor logic
  - shell correction proxy δB = -λ·S(Z,N)
- **Why it’s claimable**: Applied: a method to rank fuels/pathways/targets and to encode constraints into a reactor optimization loop.
- **Evidence (Lean)**:
  - `IndisputableMonolith/Fusion/NuclearBridge.lean`
  - `IndisputableMonolith/Fusion/ReactionNetwork.lean`
  - `IndisputableMonolith/Fusion/ReactionNetworkRates.lean`
  - `IndisputableMonolith/Fusion/BindingEnergy.lean`
- **Evidence (Python)**:
  - `fusion/simulator/nuclear/magic_numbers.py`
  - `fusion/simulator/nuclear/reaction_network.py`
  - `fusion/simulator/nuclear/fusion_binding_energy.py` (Lean-aligned proxy)
- **Seams**:
  - this is a proxy layer; empirical calibration/validation is required for claims about real binding energies.

---

## “Repo-wide” RS innovations that may be IP-relevant (beyond Fusion)

These are not all patentable *as theory*, but they matter for filings as background and for identifying applied methods:

- **J-cost uniqueness/convexity program**: proving the uniqueness and properties of `J(x)` as the canonical symmetric convex functional.
- **Eight-tick discrete time and phase gating**: foundational timing quantization used across control constructions.
- **Recognition Operator / ledger commitment formalism**: a unifying operational semantics for state evolution + “collapse”.
- **Derived-constant program**: φ bounds (`IndisputableMonolith/Constants.lean`) and other RS constants used as “parameter-free” claims.
- **ILG / cosmology / particle-mass derivation**: if there are applied algorithms (prediction pipelines, calibration procedures), those can be protectable as methods.

For an IP pass, we should treat these as:
- **background disclosures** supporting enablement, and
- **sources of applied inventions** (e.g., calibration procedures, controllers, measurement transforms).

---

## Recommended protection mix (engineering reality)

- **Patents** (high priority): Families A–G (fusion control + diagnostics + audit + certificates).
- **Trade secrets** (selective): facility integration details, calibration maps learned from proprietary diagnostics, Jacobian sensitivity matrices, operational runbooks.
- **Copyright**: code (Lean + Python), papers, docs.

---

## Immediate next actions (to hand counsel a clean packet)

1. **Freeze an “IP baseline bundle”** (zip + SHA-256 manifest) and record its hash in your internal notebook.
2. For each family A–H, produce:
   - 1–2 page **problem → solution → measurable benefit** summary
   - diagram of the pipeline steps + where seams live
   - claim-starter bullets (method + system)
   - prior art “adjacent fields” list (to guide counsel’s search)
3. Decide which families must be filed **before** broader publication/partner sharing.

---

## Key repo references for counsel

- Fusion Lean coverage audit: `fusion/planning/FUSION_LEAN_REVIEW_CROSSCHECK.md`
- Fusion pipeline hardening: `fusion/planning/ICF_PIPELINE_HARDENING_PLAN.md`
- Public data sources plan: `fusion/planning/ICF_PUBLIC_DATA_SOURCES.md`
- Simulator entrypoint: `cd fusion && python -m simulator.selfcheck`

