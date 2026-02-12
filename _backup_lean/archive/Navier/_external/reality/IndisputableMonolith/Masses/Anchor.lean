import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Masses

/-!
# Canonical Mass Constants

This module centralises the parameter-free constants described in the mass
manuscripts. Everything lives in the `Model` layer; no proofs claim
experimental agreement.

Contents:
* `E_coh` – bridge coherence energy (φ⁻⁵ eV)
* Sector yardsticks `(B_B, r0)` encoded as powers of two and φ
* Fixed rung integers `r_i` per species (charged fermions and bosons)
* Charge-based integer map `Z` (matches Paper 1)

Downstream modules should import these definitions instead of duplicating
literals.
-/

open IndisputableMonolith.Constants

namespace Anchor

/-- Coherence energy unit: `E_coh = φ⁻⁵` (dimensionless; multiply by eV externally). -/
@[simp] noncomputable def E_coh : ℝ := Constants.phi ^ (-(5 : ℤ))

/-- Sector identifiers. -/
inductive Sector | Lepton | UpQuark | DownQuark | Electroweak
  deriving DecidableEq, Repr

/-- Frozen powers of two for each sector. -/
@[simp] def B_pow : Sector → ℤ
  | .Lepton      => -22
  | .UpQuark     => -1
  | .DownQuark   => 23
  | .Electroweak => 1

/-- Frozen φ-exponent offsets per sector. -/
@[simp] def r0 : Sector → ℤ
  | .Lepton      => 62
  | .UpQuark     => 35
  | .DownQuark   => -5
  | .Electroweak => 55

/-- Sector yardstick `A_B = 2^{B_pow} * E_coh * φ^{r0}`. -/
@[simp] noncomputable def yardstick (s : Sector) : ℝ :=
  (2 : ℝ) ^ (B_pow s) * E_coh * Constants.phi ^ (r0 s)

end Anchor

namespace Integers

/-- Generation torsion (global, representation-independent). -/
@[simp] def tau (gen : ℕ) : ℤ :=
  match gen with
  | 0 => 0
  | 1 => 11
  | _ => 17

/-- Rung integers for charged leptons. -/
@[simp] def r_lepton : String → ℤ
  | "e"   => 2
  | "mu"  => 13
  | "tau" => 19
  | _     => 0

/-- Rung integers for up-type quarks. -/
@[simp] def r_up : String → ℤ
  | "u" => 4
  | "c" => 15
  | "t" => 21
  | _   => 0

/-- Rung integers for down-type quarks. -/
@[simp] def r_down : String → ℤ
  | "d" => 4
  | "s" => 15
  | "b" => 21
  | _   => 0

/-- Rung integers for electroweak bosons (structural baseline). -/
@[simp] def r_boson : String → ℤ
  | "W" => 1
  | "Z" => 1
  | "H" => 1
  | _   => 0

end Integers

namespace ChargeIndex

/-- Integer map used by the anchor relation (Paper 1). -/
@[simp] def Z (sector : Anchor.Sector) (Q : ℚ) : ℤ :=
  let Q6 : ℤ := (6 : ℤ) * Q.num / Q.den
  match sector with
  | .Lepton      => (Q6 ^ (2 : ℕ)) + (Q6 ^ (4 : ℕ))
  | .UpQuark     => 4 + (Q6 ^ (2 : ℕ)) + (Q6 ^ (4 : ℕ))
  | .DownQuark   => 4 + (Q6 ^ (2 : ℕ)) + (Q6 ^ (4 : ℕ))
  | .Electroweak => 0

end ChargeIndex

end Masses
end IndisputableMonolith
