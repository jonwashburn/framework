# Public ICF / HEDP Data Sources We Can Use (No Facility Access)

This document answers: **“If we cannot obtain NIF/OMEGA shot diagnostics, what public data exists that we can still use?”**

## Reality Check (Rigorous)

- **Raw NIF / OMEGA shot diagnostic streams are generally not public.** Access typically requires facility user credentials and/or collaboration, and may be subject to export/security controls.
- **Publicly available data exists**, but it is usually:
  - **Simulation datasets** released for ML/surrogate modeling, and/or
  - **Derived / aggregated** values in papers (tables, plots), not the underlying shot files.

This is still valuable: it lets us build and harden the **end-to-end RS control/analysis pipeline** (ingest → compute \(C_\sigma\) and other metrics → produce audit artifacts), while cleanly separating what is **model-validated** vs **facility-validated**.

---

## Best “plug-in-now” public dataset: LLNL JAG (simulation) + tooling

### What it is

LLNL released a **public ICF simulation dataset** from the **JAG** (“thermodynamic ignition target performance”) model family for multi-modal scientific ML.

### Why it helps us

Even though it’s **simulation** (not facility shots), it gives us:

- A large corpus of “shot-like” records
- **Images** (e.g., synthetic observables) and **scalar outputs**
- Input parameter vectors

That’s enough to:

- Implement and validate **diagnostic ingestion** plumbing
- Implement and validate **symmetry feature extraction** (proxy → ratios → ledger → \(C_\sigma\))
- Train/test controllers and certificate/bundle generation under stress

### Where it is (public)

- **UCSD Library Digital Collections (DOI landing)**: `https://library.ucsd.edu/dc/object/bb5534097t`
  - DOI: `https://doi.org/10.6075/J0RV0M27`
- **GitHub (LLNL)**: `https://github.com/LLNL/macc`
  - The README describes a dataset tarball containing **10K images + scalars + input parameters** (stored as `.npy` arrays).

### Critical caveat (do not blur this)

Using JAG data validates **our code path and certificates** against a known public model distribution.

It does **not** validate RS coherence claims against **nature** or a facility.

---

## Secondary “public” sources (lower leverage, but real-world adjacent)

### Published papers (tables/figures)

Many ICF papers contain:

- Yield (sometimes),
- \(T_i\) estimates (sometimes),
- Symmetry metrics (sometimes \(P_2/P_0\), \(P_4/P_0\), etc.),
- Hohlraum/capsule and laser drive summaries.

These can be **digitized** into a small “paper-derived dataset”, but they almost never include the full timing per beam/quad needed to compute \(C_\phi\) the way we want.

### Facility user guides / specs

Public guides can bound:

- Typical jitter/skew envelopes,
- Diagnostic modalities and definitions,
- Measurement conventions.

This supports the **seam policy** (what’s asserted vs kernel-checked), but it’s not shot data.

---

## What we do next (if you want to proceed with only public data)

1. Add an **optional loader/adapter** for the JAG `.npy` dataset to `rs_fusion_simulator/`.
2. Add a “public data ingest demo” that:
   - loads records,
   - extracts **P2/P0 and P4/P0** when possible (dataset-provided columns, or image-based Legendre fit),
   - computes \(C_\sigma\) using the existing ledger code,
   - emits a certificate bundle that explicitly labels the data source and seams.

### Implemented in this repo

- **Image-based P2/P4 extraction (seam)**: `rs_fusion_simulator/control/icf_modes.py`
  - Boundary ray-cast → fit even Legendre modes → reports P2/P0 and P4/P0
- **JAG demo modes**: `python -m rs_fusion_simulator.control.jag_demo --mode-source image_p2p4 ...`
- **Paper-digitized modes CSV ingest**: `python -m rs_fusion_simulator.control.paper_modes_demo --csv ...`

### Generic ingestion for *any* public image dataset

If you can obtain *any* public radiographs / hotspot images (even outside fusion),
we can still exercise the diagnostic pipeline end-to-end by ingesting image folders:

- **Adapter**: `rs_fusion_simulator/control/image_folder_dataset.py`
- **Demo**: `python -m rs_fusion_simulator.control.image_folder_demo --dir /path/to/images --out-dir /path/to/artifacts`

This is the fastest path to stress-test robustness before facility access.

### Candidate public sources to check (often “open” but not shot-stream complete)

- **LLNL Open Data Initiative**: `https://data-science.llnl.gov/open-data-initiative`
- **Calisphere collection (LLNL Open Data Initiative)**: `https://calisphere.org/collections/27558/`
- **DOE OSTI / DOE CODE / datasets**: `https://www.osti.gov/` (search for HEDP/ICF datasets; many are docs, some are data)
- **LaserNetUS resources**: `https://lasernetus.org/` (often tooling/docs; occasionally data pointers)

If any of these provide image bundles (PNG/JPG) or arrays (NPY/NPZ/HDF5), we can ingest immediately via:
`python -m rs_fusion_simulator.control.image_folder_demo --dir ... --out-dir ...`
