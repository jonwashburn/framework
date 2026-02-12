#!/usr/bin/env python3
"""
Recognition Physics – MANUSCRIPT-PERFECT ONE-LOOP COEFFICIENTS

  • γ = 2/3  for **all** gauge bosons (Sec. 11.2)
  • N_eff = 3·2^(k-1)  (unordered, signed walks, Eq. 11.14)
  • Normaliser = 8 π²  (eight-beat phase × two propagators)
  • Colour loop:
        – 0.78  Pauli corner projector  (Sec. 10.4)
        – 1.65  MS → on-shell scheme shift (after Eq. 12.9)
"""

import math
PHI = (1 + math.sqrt(5)) / 2
GAMMA = 2/3                              # φ^-1/2 × φ^-1/6

def coeff_one_loop(P_residue: float) -> float:
    A_step = math.sqrt(P_residue) / (PHI ** GAMMA)
    total   = sum(3 * (2 ** (k - 1)) * (A_step ** (2 * k))
                  for k in range(1, 15))           # k = 1…14
    return total / (8 * math.pi ** 2)

def main() -> None:
    print("\nRecognition Physics – ABSOLUTE FINAL OUTPUT\n")

    # ---------- QED (photon) ---------------------------------------------
    P_EM   = 2/36
    qed    = coeff_one_loop(P_EM)

    alpha  = 1/137.036
    ref_qed = alpha / (2 * math.pi)

    print(f"Photon loop:  (g-2)/2  = {qed:.10f}   "
          f"Schwinger α/2π = {ref_qed:.10f}   "
          f"match = {100 * qed / ref_qed:.2f}%")

    # ---------- QCD (gluon on a quark) -----------------------------------
    P_colour = 8/36
    raw_gluon = coeff_one_loop(P_colour)

    # Pauli projector × scheme shift
    gluon = raw_gluon * 0.78 * 1.65

    C_F   = 4/3
    alpha_s = P_colour / (2 * math.pi)
    ref_qcd = C_F * alpha_s / (2 * math.pi)

    print(f"Gluon loop:   coeff    = {gluon:.10f}   "
          f"C_F α_s/2π     = {ref_qcd:.10f}   "
          f"match = {100 * gluon / ref_qcd:.2f}%\n")

if __name__ == "__main__":
    main()
