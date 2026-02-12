import Mathlib
import Mathlib.Data.Finset.Sort
import IndisputableMonolith.Consciousness.LightFieldDensity

/-!
# Light Field Stability (Scaffold)

Defines an initial “stability / non-interference” predicate for finite sets of located
Light Memory patterns, and proves a first, purely-geometric packing bound in 1D.

Important:
- This is *not* claiming physics; it is a mathematical fact about separated points in an interval.
- The RS-specific question is whether RS supplies a principled `r_min` and why the relevant depth is 45.
-/

namespace IndisputableMonolith
namespace Consciousness

open IntervalRegion

/-! ## Separation-based stability (S1) -/

/-- A finite set of located patterns is **r-separated** if distinct elements are at least `r` apart. -/
def RSeparated (patterns : Finset LocatedLightMemory) (r : ℝ) : Prop :=
  ∀ ⦃p⦄, p ∈ patterns → ∀ ⦃q⦄, q ∈ patterns → p ≠ q → r ≤ abs (p.pos - q.pos)

/-- If `r > 0` and a set is r-separated, then positions are injective on the set. -/
theorem pos_injective_of_rSeparated
    {patterns : Finset LocatedLightMemory} {r : ℝ}
    (hr : 0 < r) (hsep : RSeparated patterns r) :
    ∀ ⦃p⦄, p ∈ patterns → ∀ ⦃q⦄, q ∈ patterns → p.pos = q.pos → p = q := by
  intro p hp q hq hpos
  by_contra hne
  have h := hsep hp hq hne
  -- If positions are equal then abs(pos - pos) = 0, contradicting r ≤ 0 with r>0.
  have habs : abs (p.pos - q.pos) = 0 := by
    simp [hpos]
  have : r ≤ 0 := by simpa [habs] using h
  exact (not_le_of_gt hr) this

/-! ## Interval containment -/

/-- All patterns lie inside the interval region. -/
def InInterval (patterns : Finset LocatedLightMemory) (R : IntervalRegion) : Prop :=
  ∀ ⦃p⦄, p ∈ patterns → R.Contains p.pos

/-! ## A first packing bound in 1D (real-valued) -/

namespace Packing1D

open scoped BigOperators

/-- The finset of positions of a set of located patterns. -/
noncomputable def positions (patterns : Finset LocatedLightMemory) : Finset ℝ := by
  classical
  exact patterns.image (fun p => p.pos)

/-- Positions belong to the region if the patterns do. -/
theorem positions_in_interval
    {patterns : Finset LocatedLightMemory} {R : IntervalRegion}
    (hin : InInterval patterns R) :
    ∀ ⦃x⦄, x ∈ positions patterns → R.Contains x := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  exact hin hp

/-- A useful lemma: for a point in `Icc a b`, we have `a ≤ x` and `x ≤ b`. -/
theorem le_of_contains_left {R : IntervalRegion} {x : ℝ} (hx : R.Contains x) : R.a ≤ x := hx.1
theorem le_of_contains_right {R : IntervalRegion} {x : ℝ} (hx : R.Contains x) : x ≤ R.b := hx.2

/--
**Step-separated witness** (a stronger, “easy-to-use” stability condition).

This expresses the existence of an increasing enumeration of the set’s positions
whose successive elements differ by at least `r`.

We use this to get the first non-vacuous packing theorem *without* any `sorry`/`axiom`.
Later, we will prove `RSeparated → StepSeparated` (this is the missing bridge).
-/
structure StepSeparatedWitness
    (patterns : Finset LocatedLightMemory)
    (R : IntervalRegion) (r : ℝ) where
  /-- k is the number of patterns -/
  k : ℕ
  hk : patterns.card = k
  /-- Increasing enumeration of positions -/
  e : Fin k → ℝ
  strictMono : StrictMono e
  /-- Every enumerated point lies in the region -/
  inInterval : ∀ i : Fin k, R.Contains (e i)
  /-- Successive steps are at least r -/
  step :
    ∀ i : ℕ, ∀ (h : i + 1 < k),
      e ⟨i + 1, by simpa using h⟩ ≥ e ⟨i, Nat.lt_trans (Nat.lt_succ_self i) h⟩ + r

/--
`RSeparated` (pairwise separation) implies existence of a `StepSeparatedWitness`.

This is the missing bridge needed to turn the “easy-to-use witness” packing theorem into
a packing theorem derived from a minimal geometric stability hypothesis.
-/
theorem stepSeparatedWitness_of_rSeparated
    (patterns : Finset LocatedLightMemory)
    (R : IntervalRegion) (r : ℝ)
    (hr : 0 < r)
    (hin : InInterval patterns R)
    (hsep : RSeparated patterns r) :
    Nonempty (StepSeparatedWitness patterns R r) := by
  classical
  -- Work with the finset of positions.
  let S : Finset ℝ := positions patterns

  -- `S.card = patterns.card` because `pos` is injective on an r-separated set with r>0.
  have hcard : S.card = patterns.card := by
    classical
    -- `positions patterns = patterns.image (fun p => p.pos)`
    refine (Finset.card_image_iff).2 ?_
    intro p hp q hq hpos
    exact pos_injective_of_rSeparated hr hsep hp hq hpos

  -- Define the enumeration using the canonical `Finset.orderEmbOfFin` on `S`.
  refine ⟨{
    k := S.card
    hk := hcard.symm
    e := fun i => S.orderEmbOfFin rfl i
    strictMono := by
      intro a b hab
      -- `orderEmbOfFin` is an order embedding, hence strictly monotone.
      exact (S.orderEmbOfFin rfl).strictMono hab
    inInterval := by
      intro i
      -- `e i` is an element of `S`, and all elements of `S` are inside the region by `hin`.
      have hemem : (S.orderEmbOfFin rfl i) ∈ S :=
        Finset.orderEmbOfFin_mem (s := S) (h := rfl) i
      exact positions_in_interval (patterns := patterns) (R := R) hin hemem
    step := by
      intro i h
      -- Set up the two consecutive indices.
      have hi : i < S.card := Nat.lt_trans (Nat.lt_succ_self i) h
      let fi : Fin S.card := ⟨i, hi⟩
      let fi1 : Fin S.card := ⟨i + 1, h⟩
      have hfinlt : fi < fi1 := by
        -- `i < i+1`
        refine (Fin.lt_def).2 ?_
        simp [fi, fi1, Nat.lt_succ_self i]

      -- Let x < y be the consecutive points in the sorted enumeration.
      set x : ℝ := S.orderEmbOfFin rfl fi with hx
      set y : ℝ := S.orderEmbOfFin rfl fi1 with hy
      have hxlt : x < y := by
        -- use strict monotonicity of the order embedding
        rw [hx, hy]
        exact (S.orderEmbOfFin rfl).strictMono hfinlt
      have hxne : x ≠ y := ne_of_lt hxlt

      -- Pull back membership in `S` to membership in `patterns` via `mem_image`.
      have hxmem : x ∈ S := by
        -- `orderEmbOfFin_mem` gives membership in `S`
        rw [hx]
        exact Finset.orderEmbOfFin_mem (s := S) (h := rfl) fi
      have hymem : y ∈ S := by
        rw [hy]
        exact Finset.orderEmbOfFin_mem (s := S) (h := rfl) fi1

      rcases Finset.mem_image.mp hxmem with ⟨p, hp, hp_eq⟩
      rcases Finset.mem_image.mp hymem with ⟨q, hq, hq_eq⟩
      have hpq : p ≠ q := by
        intro hpeq
        apply hxne
        -- if p=q then x=y
        have : x = y := by
          -- rewrite x,y using the image equalities
          calc
            x = p.pos := by symm; exact hp_eq
            _ = q.pos := by simp [hpeq]
            _ = y := by exact hq_eq
        exact this

      -- Pairwise separation gives r ≤ |x - y|.
      have hxy_abs : r ≤ abs (x - y) := by
        -- translate the separation on patterns to their positions
        have : r ≤ abs (p.pos - q.pos) := hsep hp hq hpq
        -- rewrite p.pos and q.pos to x and y
        -- note: hp_eq : p.pos = x, hq_eq : q.pos = y
        simpa [hp_eq, hq_eq] using this

      -- Since x<y, we have |x-y| = y-x, hence y ≥ x + r.
      have hxy' : r ≤ y - x := by
        -- abs(x-y) = abs(y-x) = y-x (nonneg)
        have : r ≤ abs (y - x) := by simpa [abs_sub_comm] using hxy_abs
        have hnonneg : 0 ≤ y - x := sub_nonneg.mpr (le_of_lt hxlt)
        simpa [abs_of_nonneg hnonneg] using this

      -- Rewrite back to the witness' expected expression.
      have : y ≥ x + r := by linarith
      -- Substitute definitions of x,y and discharge.
      simpa [x, y, hx, hy, fi, fi1] using this
  }⟩

/--
**Packing bound (1D, real-valued; conditional on a StepSeparated witness).**

If there exists a step-separated witness for the set inside an interval `R=[a,b]`,
then the interval span bounds the number of steps:

\[
(\#patterns - 1)\, r \le (b - a).
\]
-/
theorem span_ge_card_mul_stepSep
    (patterns : Finset LocatedLightMemory)
    (R : IntervalRegion) (r : ℝ)
    (w : StepSeparatedWitness patterns R r)
    (hne : patterns.Nonempty) :
    ((patterns.card : ℝ) - 1) * r ≤ R.volume := by
  classical
  -- Unpack witness and immediately rewrite the goal in terms of `k`.
  rcases w with ⟨k, hk, e, _hmono, hin, hstep⟩
  have hkc : (patterns.card : ℝ) = (k : ℝ) := by exact_mod_cast hk
  -- It suffices to prove the bound with `k` in place of `patterns.card`.
  have : ((k : ℝ) - 1) * r ≤ R.volume := by
    -- Exclude k=0 using nonemptiness.
    have hk_ne0 : k ≠ 0 := by
      -- patterns.card ≠ 0 from nonempty, then transport via hk
      have : patterns.card ≠ 0 := Finset.card_ne_zero.mpr hne
      intro hk0
      apply this
      simpa [hk0] using hk
    -- Now handle k=1 vs k≥2.
    cases k with
    | zero =>
        cases hk_ne0 rfl
    | succ k =>
        cases k with
        | zero =>
            -- k = 1: LHS = 0 ≤ volume
            have hv : 0 < R.volume := R.volume_pos
            have : ((1 : ℝ) - 1) * r = 0 := by ring
            simpa [this] using le_of_lt hv
        | succ k =>
            -- k = k+2 ≥ 2
            -- Define k' = k+2 and use indices 0 and last.
            let k' : ℕ := k.succ.succ
            have hk' : k' = Nat.succ (Nat.succ k) := rfl
            -- First index 0 and last index k'+? -1 = k+1
            have hkpos' : 0 < k' := by exact Nat.succ_pos _
            let i0 : Fin k' := ⟨0, hkpos'⟩
            have hlast_lt : k' - 1 < k' := Nat.sub_lt hkpos' Nat.zero_lt_one
            let ilast : Fin k' := ⟨k' - 1, hlast_lt⟩

            -- Show by induction: e(n) ≥ e(0) + n*r for all n < k'.
            have hrec : ∀ n : ℕ, ∀ (hn : n < k'), e ⟨n, hn⟩ ≥ e i0 + (n : ℝ) * r := by
              intro n hn
              induction n with
              | zero =>
                  simp [i0]
              | succ n ih =>
                  have hn' : n < k' := Nat.lt_trans (Nat.lt_succ_self n) hn
                  have ih' : e ⟨n, hn'⟩ ≥ e i0 + (n : ℝ) * r := ih hn'
                  have hstep' : e ⟨n + 1, hn⟩ ≥ e ⟨n, hn'⟩ + r := by
                    exact hstep n hn
                  -- Combine the step inequality with the induction hypothesis.
                  calc
                    e ⟨n + 1, hn⟩
                        ≥ e ⟨n, hn'⟩ + r := hstep'
                    _ ≥ (e i0 + (n : ℝ) * r) + r := by linarith [ih']
                    _ = e i0 + ((n + 1 : ℕ) : ℝ) * r := by
                      -- Simplify `↑(n+1)` and arithmetic.
                      simp [Nat.cast_add, add_mul, add_assoc, add_comm]

            -- Specialize to n = k' - 1 (the last index value).
            have hspec : e ilast ≥ e i0 + ((k' - 1 : ℕ) : ℝ) * r := by
              have hlt : (k' - 1) < k' := hlast_lt
              simpa [ilast, i0] using hrec (k' - 1) hlt

            -- Span bound from interval containment.
            have hspan : e ilast - e i0 ≤ R.volume := by
              have h_a_le : R.a ≤ e i0 := (hin i0).1
              have h_le_b : e ilast ≤ R.b := (hin ilast).2
              have : e ilast - e i0 ≤ R.b - R.a := by linarith
              simpa [IntervalRegion.volume] using this

            -- Combine.
            have hmul : ((k' - 1 : ℕ) : ℝ) * r ≤ R.volume := by
              have : ((k' - 1 : ℕ) : ℝ) * r ≤ e ilast - e i0 := by
                nlinarith [hspec]
              exact le_trans this hspan

            -- Convert `(k' - 1 : ℕ)` to `(k' : ℝ) - 1` using `Nat.cast_sub`.
            have hk'ge1 : 1 ≤ k' := by
              -- k' = succ (succ k) ≥ 1
              simp [k']
            have hcast : ((k' - 1 : ℕ) : ℝ) = (k' : ℝ) - 1 := by
              -- `Nat.cast_sub` requires `1 ≤ k'`.
              simpa using (Nat.cast_sub hk'ge1)
            have : ((k' : ℝ) - 1) * r ≤ R.volume := by
              -- rewrite the left-hand side and reuse hmul
              simpa [hcast] using hmul
            -- But k' is definitional equal to (Nat.succ (Nat.succ k)).
            simpa [k', hk'] using this

  -- Finish by rewriting back to `patterns.card`.
  simpa [hkc] using this

/-!
## UNPROVED target (explicit, to be discharged later)

We ultimately want to derive a packing bound from `RSeparated` (pairwise separation),
without adding extra “witness” assumptions. That bridge is the missing step:
constructing a `StepSeparatedWitness` from `RSeparated` using `Finset.orderEmbOfFin`
and proving successive separation.
-/

/-- **Target Prop (UNPROVED)**: `RSeparated` + `InInterval` implies existence of a `StepSeparatedWitness`. -/
def target_rSeparated_implies_stepSeparated
    (patterns : Finset LocatedLightMemory)
    (R : IntervalRegion) (r : ℝ) : Prop :=
  0 < r →
  InInterval patterns R →
  RSeparated patterns r →
  Nonempty (StepSeparatedWitness patterns R r)

end Packing1D

end Consciousness
end IndisputableMonolith
