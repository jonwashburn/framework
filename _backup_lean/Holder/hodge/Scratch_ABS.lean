import Hodge.Basic

-- Testing abs sum lemma names
example {ι : Type*} [Fintype ι] (f : ι → ℝ) : |∑ i : ι, f i| ≤ ∑ i : ι, |f i| := by
  exact Finset.abs_sum_le_sum_abs _ _
