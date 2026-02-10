# Anti-Gravity Theory Documents

This folder contains the theoretical foundations and mathematical derivations for bandwidth-limited gravity propulsion.

## Primary Documents

### Bandwidth-Limited-Gravity-Propulsion.tex
**Status:** Complete monograph (766 lines)  
**Authors:** Recognition Science Institute  
**Purpose:** Rigorous derivation of thrust equations and engineering specifications

This LaTeX document provides:
- Eight axioms of the cosmic ledger framework
- Derivation of recognition weight field equations
- Galaxy rotation curve validation (175 SPARC galaxies)
- Thrust-to-power scaling laws reaching 0.3 N/kW
- Three propulsion architectures (cryogenic, dielectric, metamaterial)
- Phased experimental roadmap (1 mN → 100 mN → 10 N)

#### Key Equations Referenced in Products
- **Thrust formula:** Equation (7.1) - `T ≈ M a₀ Δw`
- **Power requirement:** Equation (7.3) - `P_drive = ωU/Q + ΔU/τ_mod`
- **Thrust-to-power ratio:** Equation (7.4) - `T/P ≈ Ma₀Q/(ωU)`

#### Build Instructions
```bash
# Compile to PDF
latexmk -pdf Bandwidth-Limited-Gravity-Propulsion.tex

# Clean auxiliary files
latexmk -c
```

#### Cross-References
This document underpins the metrics quoted in:
- `../INNOVATIONS.md` - All thrust and power figures
- `../products/GravLift-Personal-Hover-Platform/README.md` - 200 kW/ton claim
- `../products/MicroG-LabKit/README.md` - Recognition weight physics

## Planned Additions
- `recognition_weight_derivation.tex` - Simplified 10-page derivation
- `thrust_optimization.nb` - Mathematica notebook for cavity design
- `sparc_rotation_fits.py` - Galaxy curve fitting code

---

*Last updated: 2025-06-24* 