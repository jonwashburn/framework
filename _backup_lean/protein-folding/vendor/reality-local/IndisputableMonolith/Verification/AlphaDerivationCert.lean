import Mathlib
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Constants.AlphaDerivation

/-!
# Alpha Derivation Certificate (no hard-coded numeric match)

This certificate packages the *symbolic provenance* of the electromagnetic coupling
formula used in `IndisputableMonolith.Constants.Alpha`:

- the “magic numbers” (11, 102, 103) come from `D=3` cube combinatorics and a fixed
  crystallographic constant (17 wallpaper groups),
- and the assembled `Constants.alphaInv` equals the constructive expression
  `Constants.AlphaDerivation.alphaInv_derived`.

Importantly, this cert does **not** assert any decimal “matches CODATA” equalities.
Those numeric checks (if desired) live in `Constants/AlphaNumericsScaffold.lean`.
-/

namespace IndisputableMonolith
namespace Verification
namespace AlphaDerivation

open IndisputableMonolith.Constants

structure AlphaDerivationCert where
  deriving Repr

@[simp] def AlphaDerivationCert.verified (_c : AlphaDerivationCert) : Prop :=
  -- Derived combinatorial constants (D=3 cube):
  (IndisputableMonolith.Constants.AlphaDerivation.geometric_seed_factor = 11)
  ∧ (IndisputableMonolith.Constants.AlphaDerivation.seam_denominator
        IndisputableMonolith.Constants.AlphaDerivation.D = 102)
  ∧ (IndisputableMonolith.Constants.AlphaDerivation.seam_numerator
        IndisputableMonolith.Constants.AlphaDerivation.D = 103)
  ∧
  -- Alignment between the public Constants formula and the constructive derivation:
  (IndisputableMonolith.Constants.alpha_seed =
      IndisputableMonolith.Constants.AlphaDerivation.geometric_seed)
  ∧ (IndisputableMonolith.Constants.delta_kappa =
      IndisputableMonolith.Constants.AlphaDerivation.curvature_term)
  ∧ (IndisputableMonolith.Constants.alphaInv =
      IndisputableMonolith.Constants.AlphaDerivation.alphaInv_derived)

@[simp] theorem AlphaDerivationCert.verified_any (c : AlphaDerivationCert) :
    AlphaDerivationCert.verified c := by
  refine And.intro ?h11 (And.intro ?h102 (And.intro ?h103 (And.intro ?hSeed (And.intro ?hKappa ?hInv))))
  · -- 11
    exact IndisputableMonolith.Constants.AlphaDerivation.geometric_seed_factor_eq_11
  · -- 102
    exact IndisputableMonolith.Constants.AlphaDerivation.seam_denominator_at_D3
  · -- 103
    exact IndisputableMonolith.Constants.AlphaDerivation.seam_numerator_at_D3
  · -- alpha_seed = geometric_seed
    have hgeom :
        IndisputableMonolith.Constants.AlphaDerivation.geometric_seed =
          4 * Real.pi * 11 :=
      IndisputableMonolith.Constants.AlphaDerivation.geometric_seed_eq
    -- hgeom.symm : 4π·11 = geometric_seed
    simpa [IndisputableMonolith.Constants.alpha_seed] using hgeom.symm
  · -- delta_kappa = curvature_term
    have hk :
        IndisputableMonolith.Constants.AlphaDerivation.curvature_term =
          (-(103 : ℝ) / (102 * Real.pi ^ 5)) :=
      IndisputableMonolith.Constants.AlphaDerivation.curvature_term_eq
    simpa [IndisputableMonolith.Constants.delta_kappa] using hk.symm
  · -- alphaInv = alphaInv_derived
    have hSeed :
        IndisputableMonolith.Constants.alpha_seed =
          IndisputableMonolith.Constants.AlphaDerivation.geometric_seed := by
      have hgeom :
          IndisputableMonolith.Constants.AlphaDerivation.geometric_seed =
            4 * Real.pi * 11 :=
        IndisputableMonolith.Constants.AlphaDerivation.geometric_seed_eq
      simpa [IndisputableMonolith.Constants.alpha_seed] using hgeom.symm
    have hKappa :
        IndisputableMonolith.Constants.delta_kappa =
          IndisputableMonolith.Constants.AlphaDerivation.curvature_term := by
      have hk :
          IndisputableMonolith.Constants.AlphaDerivation.curvature_term =
            (-(103 : ℝ) / (102 * Real.pi ^ 5)) :=
        IndisputableMonolith.Constants.AlphaDerivation.curvature_term_eq
      simpa [IndisputableMonolith.Constants.delta_kappa] using hk.symm
    -- Both definitions are `seed - (f_gap + curvature)`.
    unfold IndisputableMonolith.Constants.alphaInv
    unfold IndisputableMonolith.Constants.AlphaDerivation.alphaInv_derived
    rw [hSeed, hKappa]

end AlphaDerivation
end Verification
end IndisputableMonolith
