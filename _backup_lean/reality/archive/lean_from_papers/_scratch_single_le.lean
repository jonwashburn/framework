import Mathlib
import IndisputableMonolith.Constants.GapWeight.Formula

namespace IndisputableMonolith.Constants.GapWeight

open scoped BigOperators

example :
    phiDFTAmplitude (1 : Fin 8) * geometricWeight (1 : Fin 8) ≤ w8_dft_candidate := by
  unfold w8_dft_candidate
  have h_mem : (1 : Fin 8) ∈ Finset.filter (· ≠ 0) Finset.univ := by decide
  have h_nonneg :
      ∀ k ∈ Finset.filter (fun k : Fin 8 => k ≠ 0) Finset.univ,
        0 ≤ phiDFTAmplitude k * geometricWeight k := by
    intro k hk
    exact mul_nonneg (phiDFTAmplitude_nonneg k) (geometricWeight_nonneg k)
  -- `single_le_sum` wants the binder form `∑ x ∈ s, f x`.
  simpa using (Finset.single_le_sum (s := Finset.filter (fun k : Fin 8 => k ≠ 0) Finset.univ)
    (f := fun k : Fin 8 => phiDFTAmplitude k * geometricWeight k)
    h_nonneg h_mem)

end IndisputableMonolith.Constants.GapWeight
