import Mathlib

/-!
# Micro-Move Normal Forms

Canonical normal form for micro-move coefficient tables supporting DREAM scaffolding.
-/

namespace IndisputableMonolith
namespace Ethics
namespace Virtues

open scoped Classical BigOperators

open Finset

/-- Primitive generators in fixed canonical order. -/
inductive Primitive
  | Love | Justice | Forgiveness | Wisdom | Courage | Temperance | Prudence
  | Compassion | Gratitude | Patience | Humility | Hope | Creativity | Sacrifice
  deriving DecidableEq, Repr

/-- Canonical primitive order as a list. -/
def primitiveOrderList : List Primitive :=
  [ Primitive.Love, Primitive.Justice, Primitive.Forgiveness,
    Primitive.Wisdom, Primitive.Courage, Primitive.Temperance,
    Primitive.Prudence, Primitive.Compassion, Primitive.Gratitude,
    Primitive.Patience, Primitive.Humility, Primitive.Hope,
    Primitive.Creativity, Primitive.Sacrifice ]

lemma primitive_mem_order (p : Primitive) : p ∈ primitiveOrderList := by
  cases p <;> decide

lemma primitiveOrderList_nodup : primitiveOrderList.Nodup := by
  dsimp [primitiveOrderList]
  decide

/-- Micro moves: (pair scope, primitive, coefficient). -/
structure MicroMove where
  pair : ℕ
  primitive : Primitive
  coeff : ℝ

namespace MicroMove

/-- Canonical micro-move normal form: coefficient table with finite support. -/
structure NormalForm where
  supportPairs : Finset ℕ
  coeff : ℕ → Primitive → ℝ
  zero_outside : ∀ {pair prim}, pair ∉ supportPairs → coeff pair prim = 0
  nontrivial : ∀ {pair}, pair ∈ supportPairs → ∃ prim, coeff pair prim ≠ 0

namespace NormalForm

/-- Canonical ordered list of supported pairs (ascending). -/
noncomputable def pairList (nf : NormalForm) : List ℕ :=
  nf.supportPairs.sort (· ≤ ·)

lemma pairList_mem {nf : NormalForm} {pair : ℕ} :
    pair ∈ pairList nf ↔ pair ∈ nf.supportPairs := by
  unfold pairList
  simpa using (Finset.mem_sort (r := (· ≤ ·)) (s := nf.supportPairs) (a := pair))

lemma pairList_nodup (nf : NormalForm) : (pairList nf).Nodup := by
  unfold pairList
  simpa using (Finset.sort_nodup (· ≤ ·) nf.supportPairs)

/-- Micro-moves for a single pair. -/
noncomputable def rowMoves (nf : NormalForm) (pair : ℕ) : List MicroMove :=
  primitiveOrderList.filterMap (fun prim =>
    if nf.coeff pair prim = 0 then none
    else some ⟨pair, prim, nf.coeff pair prim⟩)

/-- Canonical ordered list of micro-moves. -/
noncomputable def toMoves (nf : NormalForm) : List MicroMove :=
  (pairList nf).flatMap (rowMoves nf)

/-- Aggregate coefficient for `(pair, primitive)` extracted from a move list. -/
noncomputable def aggCoeff (moves : List MicroMove) (pair : ℕ) (prim : Primitive) : ℝ :=
  ((moves.filter fun m => m.pair = pair ∧ m.primitive = prim).map (·.coeff)).sum

/-- Build NormalForm from a move list (aggregates coefficients). -/
noncomputable def ofMicroMoves (moves : List MicroMove) : NormalForm where
  supportPairs := (moves.map (·.pair)).toFinset.filter (fun k =>
    ∃ prim, aggCoeff moves k prim ≠ 0)
  coeff := aggCoeff moves
  zero_outside := by
    classical
    intro pair prim hnot
    have hcond : ¬ ((pair ∈ (moves.map (·.pair)).toFinset) ∧
        ∃ prim, aggCoeff moves pair prim ≠ 0) := by
      simpa [supportPairs, Finset.mem_filter] using hnot
    by_cases hmem : pair ∈ (moves.map (·.pair)).toFinset
    · have hzero : aggCoeff moves pair prim = 0 := by
        by_contra hne
        exact hcond ⟨hmem, ⟨prim, hne⟩⟩
      simpa [hzero]
    · have : (moves.filter fun m => m.pair = pair ∧ m.primitive = prim) = [] := by
        apply List.filter_eq_nil.mpr
        intro m hm hpred
        have hpair : pair ∈ (moves.map (·.pair)).toFinset := by
          refine List.mem_toFinset.mpr ?_
          refine List.mem_map.mpr ?_
          refine ⟨m, hm, ?_⟩
          simpa [hpred.1]
        exact (hmem hpair).elim
      unfold aggCoeff
      simpa [this]
  nontrivial := by
    intro pair hmem
    have : ∃ prim, aggCoeff moves pair prim ≠ 0 :=
      (Finset.mem_filter.mp hmem).2
    exact this

/-- Every micro-move generated for `pair` stays within that pair scope. -/
lemma rowMoves_pair {nf : NormalForm} {pair : ℕ} {m : MicroMove}
    (hm : m ∈ rowMoves nf pair) : m.pair = pair := by
  classical
  unfold rowMoves at hm
  rcases List.mem_filterMap.mp hm with ⟨prim, _, hprim⟩
  by_cases hcoeff : nf.coeff pair prim = 0
  · simp [hcoeff] at hprim
  · simpa [hcoeff] using hprim

/-- If a coefficient is non-zero, the corresponding micro-move appears in the row. -/
lemma rowMoves_mem_of_coeff_ne_zero {nf : NormalForm} {pair : ℕ} {prim : Primitive}
    (hcoeff : nf.coeff pair prim ≠ 0) :
    ⟨pair, prim, nf.coeff pair prim⟩ ∈ rowMoves nf pair := by
  classical
  unfold rowMoves
  have : prim ∈ primitiveOrderList := primitive_mem_order prim
  simpa [hcoeff] using List.mem_filterMap.mpr (by exact ⟨prim, this, by simp [hcoeff]⟩)

/-- Auxiliary lemma: sum over a primitive list. -/
private lemma aggCoeff_rowMoves_aux
    (nf : NormalForm) (pair : ℕ) (prim : Primitive) :
    ((primitiveOrderList.filterMap fun q =>
          if hq : nf.coeff pair q = 0 then none
          else some ⟨pair, q, nf.coeff pair q⟩)
        .filter (fun m => m.pair = pair ∧ m.primitive = prim)
        .map (·.coeff)).sum
      = if prim ∈ primitiveOrderList then nf.coeff pair prim else 0 := by
  classical
  let f : Primitive → Option MicroMove :=
    fun q => if hq : nf.coeff pair q = 0 then none else some ⟨pair, q, nf.coeff pair q⟩
  have hrec :
      ∀ (l : List Primitive), l.Nodup →
        (((l.filterMap f).filter (fun m => m.pair = pair ∧ m.primitive = prim)).map (·.coeff)).sum
          = if prim ∈ l then nf.coeff pair prim else 0 := by
    refine List.recOn ?l ?base ?step
    · intro h; simp [f]
    · intro q qs ih hnodup
      rcases List.nodup_cons.mp hnodup with ⟨hq_notin, hqs⟩
      by_cases hcoeff : nf.coeff pair q = 0
      · have : f q = none := by simp [f, hcoeff]
        have := ih hqs
        simp [f, hcoeff, this, List.mem_cons] -- both cases handled by simp
      · have : f q = some ⟨pair, q, nf.coeff pair q⟩ := by simp [f, hcoeff]
        by_cases hqp : q = prim
        · subst hqp
          have hmem : prim ∉ qs := by simpa using hq_notin
          have := ih hqs
          simp [f, hcoeff, this, List.mem_cons, hmem] -- yields nf.coeff pair prim
        · have := ih hqs
          simp [f, hcoeff, this, List.mem_cons, hqp] -- reduces to tail case
  simpa [rowMoves, aggCoeff, f] using
    (hrec primitiveOrderList primitiveOrderList_nodup)

/-- Aggregated coefficient for a row equals the stored table value. -/
lemma aggCoeff_rowMoves (nf : NormalForm) (pair : ℕ) (prim : Primitive) :
    aggCoeff (rowMoves nf pair) pair prim = nf.coeff pair prim := by
  classical
  have hmem : prim ∈ primitiveOrderList := primitive_mem_order prim
  simpa [aggCoeff, rowMoves, hmem] using aggCoeff_rowMoves_aux nf pair prim

/-- Rows for distinct pairs contribute nothing to another pair's aggregation. -/
lemma aggCoeff_rowMoves_of_ne (nf : NormalForm) {pair k : ℕ} {prim : Primitive}
    (hkp : k ≠ pair) : aggCoeff (rowMoves nf k) pair prim = 0 := by
  classical
  unfold aggCoeff
  have : (rowMoves nf k).filter (fun m => m.pair = pair ∧ m.primitive = prim) = [] := by
    apply List.filter_eq_nil.mpr
    intro m hm hcond
    have hk := rowMoves_pair (nf := nf) (pair := k) (m := m) hm
    exact (hkp (hk.trans hcond.1.symm)).elim
  simp [this]

/-- Aggregation distributes over concatenation of move lists. -/
lemma aggCoeff_append (xs ys : List MicroMove) (pair : ℕ) (prim : Primitive) :
    aggCoeff (xs ++ ys) pair prim = aggCoeff xs pair prim + aggCoeff ys pair prim := by
  classical
  unfold aggCoeff
  simp [List.filter_append, List.map_append, List.sum_append, add_comm, add_left_comm, add_assoc]

/-- Aggregation over a flat-mapped list of row moves. -/
lemma aggCoeff_flatMap (nf : NormalForm) (pair : ℕ) (prim : Primitive)
    (l : List ℕ) (hl : l.Nodup) :
    aggCoeff (l.flatMap (rowMoves nf)) pair prim
      = if pair ∈ l then aggCoeff (rowMoves nf pair) pair prim else 0 := by
  classical
  refine List.recOn l ?base ?step
  · simp
  · intro k ks ih hcons
    rcases List.nodup_cons.mp hcons with ⟨hk_notin, hks⟩
    have ih' := ih hks
    have : aggCoeff (rowMoves nf k) pair prim =
        (if k = pair then aggCoeff (rowMoves nf pair) pair prim else 0) := by
      by_cases hkpair : k = pair
      · subst hkpair
        simp
      · simp [hkpair, aggCoeff_rowMoves_of_ne (nf := nf) (prim := prim) hkpair]
    simp [List.flatMap_cons, aggCoeff_append, ih', this, List.mem_cons, hk_notin] -- handles membership cases

/-- Aggregated coefficient extracted from `toMoves` equals the canonical table. -/
lemma sumCoeffs_toMoves (nf : NormalForm) (pair : ℕ) (prim : Primitive) :
    aggCoeff (toMoves nf) pair prim = nf.coeff pair prim := by
  classical
  unfold toMoves
  have hflat := aggCoeff_flatMap (nf := nf) (pair := pair) (prim := prim)
    (l := pairList nf) (hl := pairList_nodup nf)
  by_cases hpair : pair ∈ pairList nf
  · have := aggCoeff_rowMoves (nf := nf) (pair := pair) (prim := prim)
    simpa [hflat, hpair] using this
  · have hsupp : pair ∉ nf.supportPairs := by
      simpa [pairList_mem] using hpair
    have hzero := nf.zero_outside (pair := pair) (prim := prim) hsupp
    simp [hflat, hpair, hzero]

/-- Non-zero coefficients guarantee the corresponding move appears in `toMoves`. -/
lemma mem_toMoves_of_coeff_ne_zero (nf : NormalForm) {pair : ℕ} {prim : Primitive}
    (hsupp : pair ∈ nf.supportPairs) (hcoeff : nf.coeff pair prim ≠ 0) :
    ⟨pair, prim, nf.coeff pair prim⟩ ∈ toMoves nf := by
  classical
  unfold toMoves
  have hpair : pair ∈ pairList nf := (pairList_mem).2 hsupp
  exact List.mem_flatMap.mpr
    ⟨pair, hpair, rowMoves_mem_of_coeff_ne_zero (nf := nf) (pair := pair) (prim := prim) hcoeff⟩

/-- The mapped pair list produced by `toMoves` contains any supported pair with non-zero coeff. -/
lemma pair_mem_toMoves_map (nf : NormalForm) {pair : ℕ} {prim : Primitive}
    (hsupp : pair ∈ nf.supportPairs) (hcoeff : nf.coeff pair prim ≠ 0) :
    pair ∈ ((toMoves nf).map (·.pair)).toFinset := by
  classical
  have hmove := mem_toMoves_of_coeff_ne_zero (nf := nf) hsupp hcoeff
  have hmap : pair ∈ (toMoves nf).map (·.pair) := by
    refine List.mem_map.mpr ?_
    refine ⟨⟨pair, prim, nf.coeff pair prim⟩, hmove, ?_⟩
    simp
  exact List.mem_toFinset.mpr hmap

/-- Normal forms round-trip through `toMoves` and `ofMicroMoves`. -/
theorem of_toMoves (nf : NormalForm) :
    ofMicroMoves (toMoves nf) = nf := by
  classical
  ext pair prim
  · constructor
    · intro hmem
      rcases Finset.mem_filter.mp hmem with ⟨hmap, hex⟩
      rcases hex with ⟨prim', hagg⟩
      have hcoeff : nf.coeff pair prim' ≠ 0 := by
        simpa [sumCoeffs_toMoves] using hagg
      have : pair ∈ nf.supportPairs := by
        by_contra hnot
        have := nf.zero_outside (pair := pair) (prim := prim') hnot
        exact hcoeff (by simpa [sumCoeffs_toMoves] using this)
      exact this
    · intro hmem
      obtain ⟨prim', hcoeff⟩ := nf.nontrivial hmem
      have hcoeff' : nf.coeff pair prim' ≠ 0 := hcoeff
      have hmap := pair_mem_toMoves_map (nf := nf) hmem hcoeff'
      have : aggCoeff (toMoves nf) pair prim' ≠ 0 := by
        simpa [sumCoeffs_toMoves] using hcoeff'
      refine Finset.mem_filter.mpr ⟨hmap, ?_⟩
      exact ⟨prim', this⟩
  · simpa [ofMicroMoves, sumCoeffs_toMoves]

/-- The canonical pair list matches the 16-window filtered enumeration. -/
lemma pairList_eq_filtered_range (nf : NormalForm)
    (hw : nf.supportPairs ⊆ Finset.range 16) :
    pairList nf = (List.range 16).filter (fun k => k ∈ nf.supportPairs) := by
  classical
  have hset :
      ((List.range 16).filter (fun k => k ∈ nf.supportPairs)).toFinset
        = nf.supportPairs := by
    apply Finset.ext
    intro k; constructor
    · intro hk
      have hk' := List.mem_toFinset.mp hk
      rcases List.mem_filter.mp hk' with ⟨hk_range, hk_support⟩
      exact hk_support
    · intro hk
      have hk_range : k ∈ List.range 16 := by
        have : k ∈ Finset.range 16 := hw hk
        have : k < 16 := Finset.mem_range.mp this
        exact List.mem_range.mpr this
      exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hk_range, hk⟩)

  have hfin_lhs : (pairList nf).toFinset = nf.supportPairs := by
    unfold pairList
    simp
  have hperm :
      pairList nf ~ (List.range 16).filter (fun k => k ∈ nf.supportPairs) := by
    have := List.toFinset_eq_iff_perm_dedup.mpr (by simpa [hfin_lhs, hset])
    have hl : (pairList nf).dedup = pairList nf :=
      List.dedup_eq_self.mpr (pairList_nodup nf)
    have hr : ((List.range 16).filter (fun k => k ∈ nf.supportPairs)).dedup
        = (List.range 16).filter (fun k => k ∈ nf.supportPairs) :=
      List.dedup_eq_self.mpr ((List.nodup_range _).filter _)
    simpa [hl, hr] using this

  have hsorted_lhs : List.Sorted (· ≤ ·) (pairList nf) := by
    unfold pairList
    simpa using Finset.sort_sorted (· ≤ ·) nf.supportPairs
  have hsorted_rhs : List.Sorted (· ≤ ·)
      ((List.range 16).filter (fun k => k ∈ nf.supportPairs)) := by
    have := List.sorted_filter (List.sorted_range _) (fun k => k ∈ nf.supportPairs)
    simpa using this
  exact List.eq_of_perm_of_sorted hperm hsorted_lhs hsorted_rhs
end NormalForm

end MicroMove

end Virtues
end Ethics
end IndisputableMonolith
