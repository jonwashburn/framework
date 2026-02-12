import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Ring.Abs

/-!
Rounding/slow-variation lemmas used in the TeX microstructure bookkeeping.

These are purely analytic/combinatorial inequalities (no geometry/GMT) that appear around:
- `lem:slow-variation-rounding`
- `lem:slow-variation-discrepancy`

in `Hodge_REFEREE_Amir-v1.tex` (Jan 2026 referee draft).

We keep these lemmas separate from `Hodge/Kahler/Microstructure.lean` so they can be reused
without pulling in the (currently stubbed) geometric layer.
-/

noncomputable section

namespace Hodge

namespace Rounding

/-! ### Nearest-integer rounding -/

/-- **Nearest-integer rounding is 1-Lipschitz up to an additive 1**.

This is the inequality used in the TeX proof as
\[
|N_Q - N_{Q'}| \le |n_Q - n_{Q'}| + 1
\]
for the nearest-integer rounding \(N_Q := \lfloor n_Q \rceil\).

Lean uses `round : ℝ → ℤ` (round halves towards \(+\infty\)). -/
theorem abs_round_sub_round_le (x y : ℝ) :
    ((|round x - round y| : ℤ) : ℝ) ≤ |x - y| + 1 := by
  have hx : |x - (round x : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa using (abs_sub_round (α := ℝ) x)
  have hy : |y - (round y : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa using (abs_sub_round (α := ℝ) y)

  have hcast : ((|round x - round y| : ℤ) : ℝ) = |(round x : ℝ) - (round y : ℝ)| := by
    -- `Int.cast_abs` : (|z| : ℝ) = |(z:ℝ)|, and casts turn subtraction in `ℤ` into subtraction in `ℝ`.
    -- `simp` turns `((round x - round y : ℤ) : ℝ)` into `(round x : ℝ) - (round y : ℝ)`.
    simpa [sub_eq_add_neg] using (Int.cast_abs (R := ℝ) (a := round x - round y))

  have hx' : |(round x : ℝ) - x| ≤ (1 / 2 : ℝ) := by
    simpa [abs_sub_comm] using hx
  have hy' : |(round y : ℝ) - y| ≤ (1 / 2 : ℝ) := by
    simpa [abs_sub_comm] using hy

  have htri : |(round x : ℝ) - (round y : ℝ)| ≤ |x - y| + 1 := by
    have h_id :
        (round x : ℝ) - (round y : ℝ) =
          (x - y) + ((round x : ℝ) - x) + (y - (round y : ℝ)) := by
      ring
    calc
      |(round x : ℝ) - (round y : ℝ)|
          = |(x - y) + ((round x : ℝ) - x) + (y - (round y : ℝ))| := by
              rw [h_id]
      _ ≤ |(x - y) + ((round x : ℝ) - x)| + |y - (round y : ℝ)| := by
            simpa [add_assoc] using
              (abs_add_le ((x - y) + ((round x : ℝ) - x)) (y - (round y : ℝ)))
      _ ≤ (|x - y| + |(round x : ℝ) - x|) + |y - (round y : ℝ)| := by
            gcongr
            exact abs_add_le (x - y) ((round x : ℝ) - x)
      _ ≤ (|x - y| + (1 / 2 : ℝ)) + (1 / 2 : ℝ) := by
            gcongr
      _ = |x - y| + 1 := by ring

  calc
    ((|round x - round y| : ℤ) : ℝ)
        = |(round x : ℝ) - (round y : ℝ)| := hcast
    _ ≤ |x - y| + 1 := htri

/-! ### 0–1 discrepancy rounding (`N = floor(n) + ε`, ε∈{0,1}) -/

/-- A Lipschitz-style bound for floors: `⌊x⌋` is 1-Lipschitz up to an additive `1` (after casting to `ℝ`). -/
theorem abs_floor_sub_floor_le (x y : ℝ) :
    ((|Int.floor x - Int.floor y| : ℤ) : ℝ) ≤ |x - y| + 1 := by
  have hcast :
      ((|Int.floor x - Int.floor y| : ℤ) : ℝ) = |(Int.floor x : ℝ) - (Int.floor y : ℝ)| := by
    -- `Int.cast_abs` : (|z| : ℝ) = |(z:ℝ)|, and casts turn subtraction in `ℤ` into subtraction in `ℝ`.
    simpa [sub_eq_add_neg] using (Int.cast_abs (R := ℝ) (a := Int.floor x - Int.floor y))
  have hreal : |(Int.floor x : ℝ) - (Int.floor y : ℝ)| ≤ |x - y| + 1 := by
    refine (abs_sub_le_iff).2 ?_
    constructor
    · -- ⌊x⌋ - ⌊y⌋ ≤ |x-y| + 1
      have hx : (Int.floor x : ℝ) ≤ x := Int.floor_le x
      have hy : -(Int.floor y : ℝ) ≤ 1 - y := by
        have hy_lt : y < (Int.floor y : ℝ) + 1 := by
          simpa using (Int.lt_floor_add_one y)
        have : -(Int.floor y : ℝ) < 1 - y := by linarith
        exact le_of_lt this
      have hxy : (Int.floor x : ℝ) - (Int.floor y : ℝ) ≤ (x - y) + 1 := by
        linarith
      have hle : (x - y) + 1 ≤ |x - y| + 1 := by
        gcongr
        exact le_abs_self (x - y)
      exact le_trans hxy hle
    · -- ⌊y⌋ - ⌊x⌋ ≤ |x-y| + 1
      have hy : (Int.floor y : ℝ) ≤ y := Int.floor_le y
      have hx : -(Int.floor x : ℝ) ≤ 1 - x := by
        have hx_lt : x < (Int.floor x : ℝ) + 1 := by
          simpa using (Int.lt_floor_add_one x)
        have : -(Int.floor x : ℝ) < 1 - x := by linarith
        exact le_of_lt this
      have hyx : (Int.floor y : ℝ) - (Int.floor x : ℝ) ≤ (y - x) + 1 := by
        linarith
      have hle : (y - x) + 1 ≤ |x - y| + 1 := by
        have : (y - x) ≤ |x - y| := by
          -- `y - x = -(x - y)`
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (neg_le_abs (x - y))
        gcongr
      exact le_trans hyx hle
  simpa [hcast] using hreal

/-- If `ε, ε' ∈ {0,1}`, then `|ε - ε'| ≤ 1` (after casting to `ℝ`). -/
theorem abs_eps_sub_eps_le_one (ε ε' : ℤ) (hε : ε = 0 ∨ ε = 1) (hε' : ε' = 0 ∨ ε' = 1) :
    ((|ε - ε'| : ℤ) : ℝ) ≤ 1 := by
  rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> norm_num

/-- **0–1 discrepancy rounding bound**.

If we choose integers of the form `N := ⌊n⌋ + ε` with `ε ∈ {0,1}`, then variation changes by
at most an additive `2`:
\[
|N(x) - N(y)| \le |x-y| + 2.
\]

This matches the TeX estimate in Lemma `lem:slow-variation-discrepancy`. -/
theorem abs_floor_discrepancy_le (x y : ℝ) (ε ε' : ℤ)
    (hε : ε = 0 ∨ ε = 1) (hε' : ε' = 0 ∨ ε' = 1) :
    ((|Int.floor x + ε - (Int.floor y + ε')| : ℤ) : ℝ) ≤ |x - y| + 2 := by
  have htriZ :
      |(Int.floor x + ε) - (Int.floor y + ε')| ≤ |Int.floor x - Int.floor y| + |ε - ε'| := by
    have :
        (Int.floor x + ε) - (Int.floor y + ε') = (Int.floor x - Int.floor y) + (ε - ε') := by
      ring
    simpa [this] using (abs_add_le (Int.floor x - Int.floor y) (ε - ε'))
  have htriR :
      ((|(Int.floor x + ε) - (Int.floor y + ε')| : ℤ) : ℝ) ≤
        ((|Int.floor x - Int.floor y| : ℤ) : ℝ) + ((|ε - ε'| : ℤ) : ℝ) := by
    exact_mod_cast htriZ
  have hfloor : ((|Int.floor x - Int.floor y| : ℤ) : ℝ) ≤ |x - y| + 1 :=
    abs_floor_sub_floor_le x y
  have heps : ((|ε - ε'| : ℤ) : ℝ) ≤ 1 :=
    abs_eps_sub_eps_le_one ε ε' hε hε'
  have habs :
      ((|Int.floor x + ε - (Int.floor y + ε')| : ℤ) : ℝ) =
        ((|(Int.floor x + ε) - (Int.floor y + ε')| : ℤ) : ℝ) := by
    simp [sub_eq_add_neg, add_assoc, add_comm]
  linarith [htriR, hfloor, heps, habs]

end Rounding

end Hodge
