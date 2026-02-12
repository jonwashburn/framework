# Recognition Science Technology-Atlas  – Maintainer Punch-List

*(last updated: 2025-06-24)*

This document orients any future AI or human contributor who opens this repository.  It summarises **what we are building, where everything lives, and what needs to happen next.  Read this first before touching files.**

---

## 0. Mission Snapshot
The **Technology-Atlas** captures fifteen technology pillars derived from Recognition Science (RS).  Each pillar contains:
1. `INNOVATIONS.md` – ranked roadmap table (metrics, TRL, links).
2. `products/⟨Slug⟩/` – one folder per innovation.
3. `products/⟨Slug⟩/README.md` – detailed product brief.
4. `products/⟨Slug⟩/product.yaml` – machine-readable metadata.
5. Optional sub-folders: `theory/`, `prototypes/`, `regulatory/`, `references/`.

The **anti-gravity pillar (01)** is now the canonical template.  All other pillars should conform to this pattern.

---

## 1. Repository Map
| Path | Purpose |
|------|---------|
| `/` | Root of **Technology-Atlas** mono-repo. |
| `01-…` → `15-…` | Fifteen technology pillar directories. |
| `docs/templates/` | Canonical documentation templates (`PRODUCT_README_TEMPLATE.md`). |
| `docs/TRL_DEFINITIONS.md` | Repository-wide TRL reference table. |
| `scripts/` | Utility scripts (e.g. `validate_atlas.py`). |
| `INNOVATIONS_INDEX.md` | Auto-generated index linking all pillars. |
| `PROJECT_PUNCHLIST.md` | **← you are here** – rolling action list. |
| `source_code.txt` | Condensed Recognition Science reference **(critical!).** |

External repos of interest:
* `https://github.com/jonwashburn/Technology-Atlas` – this repo (default *main* branch).
* `https://github.com/jonwashburn/ym-proof` – Lean4 Yang-Mills formalisation (uses RS maths).

---

## 2. Completed so far (high-level)
* **Infrastructure**
  * Mono-repo with pillar directory skeletons.
  * Cross-pillar index & product inventory.
  * Central documentation templates & TRL definitions.
* **Anti-Gravity Pillar (01)**
  * Rich `INNOVATIONS.md` table (10 products, metrics).
  * Full product briefs for **GravLift™** and **MicroG™ LabKit**.
  * `product.yaml` metadata for both products.
  * Regulatory blueprint stub (`regulatory/anti_gravity_FAA_ISO.md`).
  * Duplicate legacy folder removed; canonical path cleaned.

---

## 3. Immediate TODOs (next 1-2 work sessions)
1. **Replicate Template to Remaining Pillars**
   * For each pillar `02-15` create:
     * `INNOVATIONS.md` with ≥5 seed products.
     * At least **one** fleshed-out product README + metadata.
   * Use `docs/templates/PRODUCT_README_TEMPLATE.md`.
2. **Metadata Validation**
   * Extend `scripts/validate_atlas.py` to parse every `product.yaml` and ensure links/metrics match `INNOVATIONS.md` rows.
3. **CI Integration**
   * Add GitHub Action: run validation script + Markdown lint on every PR.
4. **Cross-Pillar Dependency Graph**
   * Auto-generate Mermaid diagram from `dependencies:` field in `product.yaml`s and embed in repository README.
5. **Regulatory Files**
   * Create a `regulatory/` folder inside each pillar with a similar compliance table stub.
6. **Theory Resurrection**
   * Deleted theory files (`recognition_weight_derivation.tex`, etc.) should be restored or re-linked from RS manuscripts.

---

## 4. Medium-Term Tasks (this quarter)
* **Populate Remaining Product Briefs** – aim for 3 per pillar (45 total).
* **Business & Patent Sections** – expand each README with preliminary cost/BOM and IP notes.
* **Simulation & Prototype Folders** – add at least one `.py` or `.lean` proof/sim per pillar.
* **Documentation Site** – static docs build (MkDocs or Docusaurus) pulling from repo Markdown.
* **Dashboard** – simple web dashboard reading `product.yaml` to show status heat-map.

---

## 5. Important Files Worth Reading First
* `source_code.txt` – **single-file condensed RS theory (2165 lines)**.  Provides physics/maths backbone for all tech.
* `01-Anti-Gravity-Field-Propulsion/INNOVATIONS.md` – exemplar roadmap table with engineering metrics.
* `docs/templates/PRODUCT_README_TEMPLATE.md` – canonical structure for all future product docs.
* `01-Anti-Gravity-Field-Propulsion/products/GravLift-Personal-Hover-Platform/README.md` – fully populated product brief to copy.
* `scripts/validate_atlas.py` – basic repo-sanity script; extend for metadata checks.

---

## 6. Conventions Recap
* **Slug casing**: `CamelCase-with-dashes` for folder names.
* **Metrics**: Field strength (N kg⁻¹) and power-lift ratio (kW t⁻¹) mandatory in tables & YAML.
* **Metadata**: `product.yaml` lives beside README; keys: `slug`, `trl`, `target_window`, `dependencies`, `next_milestone`.
* **Links**: Use relative paths; keep tables Github-renderable.

---

## 7. Open Questions
* How to handle products shared across multiple pillars (e.g. quantum ASIC)?  Proposal: central `shared_components/` directory + symlinks.
* Should we version‐lock Recognition Science reference (`source_code.txt`) or pull from external repo to avoid divergence?
* Decide license & contribution guidelines before opening to external collaborators.

---

## 8. Contact
Maintainer: **Jonathan Washburn** – Austin, Texas – x.com/jonwashburn  
For AI agent context, cite this file as the starting waypoint.

---

> *End of punch-list.  Future contributors: commit incremental updates here whenever the roadmap changes.* 