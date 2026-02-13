import IndisputableMonolith.Measurement.RSNative.Core
import IndisputableMonolith.OctaveKernel.VoxelMeaning
import IndisputableMonolith.LightLanguage.Core

namespace IndisputableMonolith
namespace Measurement
namespace RSNative
namespace Adapters
namespace VoxelToWToken

open scoped BigOperators
open Classical

open IndisputableMonolith.OctaveKernel
open IndisputableMonolith.LightLanguage

/-!
## Voxel → WToken adapter (scaffold)

This adapter turns a `MeaningfulVoxel` (8-phase photon state) into a WToken candidate.

We provide:
- a **data-only** candidate (`WTokenData`), and
- an **optional** legalized token (`Option LegalWToken`) produced by:
  1) mean-subtraction (enforce neutrality),
  2) L² normalization (enforce unit energy),
  3) fail with `none` when the projected signal has zero energy.

STATUS: `Protocol.Status.scaffold`
- This is a generic mathematical projection, not a claim of semantic category.
- Future work can replace this with classification/decomposition against the 20 canonical WTokens.
-/

/-- Mean of an 8-phase complex signal. -/
noncomputable def mean8 (x : Fin 8 → ℂ) : ℂ :=
  ((1 / 8 : ℝ) : ℂ) * (∑ i : Fin 8, x i)

/-- Mean-free projection (neutrality enforcement). -/
noncomputable def centered (x : Fin 8 → ℂ) : Fin 8 → ℂ :=
  fun i => x i - mean8 x

lemma centered_sum_eq_zero (x : Fin 8 → ℂ) :
    (∑ i : Fin 8, centered x i) = 0 := by
  classical
  unfold centered mean8
  simp [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Energy of an 8-phase signal. -/
noncomputable def energy8 (x : Fin 8 → ℂ) : ℝ :=
  ∑ i : Fin 8, Complex.normSq (x i)

lemma energy8_nonneg (x : Fin 8 → ℂ) : 0 ≤ energy8 x := by
  unfold energy8
  apply Finset.sum_nonneg
  intro i hi
  exact Complex.normSq_nonneg _

/-- Normalize by L² energy. Requires `0 < energy8 x`. -/
noncomputable def normalize8 (x : Fin 8 → ℂ) : Fin 8 → ℂ :=
  fun i => x i / (Real.sqrt (energy8 x) : ℂ)

lemma normalize8_sum_eq_zero (x : Fin 8 → ℂ) :
    (∑ i : Fin 8, normalize8 (centered x) i) = 0 := by
  classical
  unfold normalize8
  -- turn `∑ (v i / c)` into `(∑ v i) / c`
  have hsumdiv :
      (∑ i : Fin 8, centered x i) / (Real.sqrt (energy8 (centered x)) : ℂ)
        = ∑ i : Fin 8, centered x i / (Real.sqrt (energy8 (centered x)) : ℂ) := by
    simpa using
      (Finset.sum_div (s := Finset.univ)
        (f := fun i : Fin 8 => centered x i)
        (a := (Real.sqrt (energy8 (centered x)) : ℂ)))
  have h0 : (∑ i : Fin 8, centered x i) = 0 := centered_sum_eq_zero x
  -- rewrite the goal using hsumdiv
  calc
    ∑ i : Fin 8, centered x i / (Real.sqrt (energy8 (centered x)) : ℂ)
        = (∑ i : Fin 8, centered x i) / (Real.sqrt (energy8 (centered x)) : ℂ) := by
            symm
            simpa using hsumdiv
    _ = 0 := by simp [h0]

lemma normalize8_normSq_sum_eq_one (x : Fin 8 → ℂ) (hE : 0 < energy8 x) :
    (∑ i : Fin 8, Complex.normSq (normalize8 x i)) = 1 := by
  classical
  unfold normalize8
  have hE0 : energy8 x ≠ 0 := ne_of_gt hE
  have hden : Complex.normSq (Real.sqrt (energy8 x) : ℂ) = energy8 x := by
    simp [Complex.normSq_ofReal, Real.mul_self_sqrt (energy8_nonneg x)]
  -- rewrite each term to `normSq (x i) / energy8 x`
  simp [hden]
  have hsumdiv :
      (∑ i : Fin 8, Complex.normSq (x i)) / (energy8 x)
        = ∑ i : Fin 8, Complex.normSq (x i) / (energy8 x) := by
    simpa [energy8] using
      (Finset.sum_div (s := Finset.univ)
        (f := fun i : Fin 8 => Complex.normSq (x i))
        (a := energy8 x))
  calc
    (∑ i : Fin 8, Complex.normSq (x i) / energy8 x)
        = (∑ i : Fin 8, Complex.normSq (x i)) / energy8 x := by
            symm
            simpa using hsumdiv
    _ = (energy8 x) / (energy8 x) := by simp [energy8]
    _ = 1 := by simp [hE0]

/-- Protocol: voxel→WToken projection (placeholder, falsifiable). -/
def protocol : Protocol :=
  { name := "adapter.voxel_to_wtoken"
    summary :=
      "Scaffold: project an 8-phase voxel signal to a WToken candidate by neutrality " ++
      "(mean subtraction) and L² normalization."
    status := .scaffold
    assumptions :=
      [ "A MeaningfulVoxel’s complex 8-signal is an appropriate raw carrier for WToken basis vectors."
      , "We enforce neutrality by subtracting the mean (DC component)."
      , "We enforce unit norm by dividing by √(energy) after neutrality projection."
      , "Semantic classification (mapping to one of the 20 canonical WTokens) is out of scope here."
      ]
    falsifiers :=
      [ "If the correct semantic basis is in frequency-domain (DFT) rather than time-domain, this projection is wrong."
      , "If neutrality must be enforced by a different constraint than DC mean subtraction, replace centered()."
      , "If zero-energy projected signals are physically meaningful and need handling, replace the Option-returning seam."
      ]
  }

/-- Data-only WToken candidate (always returns a value; may be illegal). -/
noncomputable def toWTokenData (v : MeaningfulVoxel) : LightLanguage.WTokenData :=
  let raw : Fin 8 → ℂ := v.toComplexSignal
  { nu_phi := 0
    ell := 0
    sigma := 0
    tau := (0 : Fin 8)
    k_perp := (0, 0, 0)
    phi_e := 0
    basis := normalize8 (centered raw)
  }

/-- Attempt to produce a *legal* WToken (neutral + normalized). Returns `none` if the
neutral-projected signal has zero energy. -/
noncomputable def toLegalWToken (v : MeaningfulVoxel) : Option LightLanguage.LegalWToken :=
  let raw : Fin 8 → ℂ := v.toComplexSignal
  let x : Fin 8 → ℂ := centered raw
  if hE : 0 < energy8 x then
    let basis : Fin 8 → ℂ := normalize8 x
    let wData : LightLanguage.WTokenData :=
      { nu_phi := 0
        ell := 0
        sigma := 0
        tau := (0 : Fin 8)
        k_perp := (0, 0, 0)
        phi_e := 0
        basis := basis
      }
    have hNeutral : (Finset.univ.sum wData.basis) = 0 := by
      -- sum(normalize8 (centered raw)) = 0 (by construction)
      have h0 : (∑ i : Fin 8, basis i) = 0 := by
        simpa [basis, x] using (normalize8_sum_eq_zero raw)
      simpa [wData] using h0
    have hNorm : (Finset.univ.sum fun i : Fin 8 => Complex.normSq (wData.basis i)) = 1 := by
      simpa [wData, basis] using normalize8_normSq_sum_eq_one x hE
    some ⟨wData, ⟨hNeutral, hNorm⟩⟩
  else
    none

/-- Legacy WToken (proof-carrying) if legalization succeeds. -/
noncomputable def toWToken (v : MeaningfulVoxel) : Option LightLanguage.WToken :=
  (toLegalWToken v).map (fun lw => lw.toWToken)

/-- Observable: voxel → optional legal WToken. -/
noncomputable def legalWToken : Observable MeaningfulVoxel (Option LightLanguage.LegalWToken) :=
  fun v =>
    { value := toLegalWToken v
      window := none
      protocol := protocol
      uncertainty := none
      notes := ["Returns none when the neutral-projected signal has zero energy."]
    }

end VoxelToWToken
end Adapters
end RSNative
end Measurement
end IndisputableMonolith


