import Mathlib
import IndisputableMonolith.Complexity.SAT.CNF
import IndisputableMonolith.Complexity.SAT.XOR
import IndisputableMonolith.Complexity.SAT.SmallBias

namespace IndisputableMonolith
namespace Complexity
namespace SAT

/-!
# Geometric XOR Family (Morton Octant Masks)

This module defines the geometric XOR family 𝓗_geo(n) which extends the linear
mask family with Morton-curve-aligned octant parity constraints.
-/

open List

/-- Morton index: interleave 3 coordinates into a single index. -/
def mortonIndex (x y z : Nat) : Nat :=
  x + y * 1000 + z * 1000000

/-- Octant level: how many octant subdivisions (0 = whole space, k = 8^k subregions). -/
abbrev OctantLevel := Nat

/-- Octant index within a level (0 to 8^level - 1). -/
abbrev OctantIndex := Nat

/-- Check if a Morton index falls within a given octant at a given level. -/
def inOctant (mortonIdx : Nat) (level : OctantLevel) (octant : OctantIndex) : Bool :=
  if level = 0 then true
  else (mortonIdx / (8 ^ (Nat.log2 mortonIdx / level + 1))) % (8 ^ level) = octant

/-- Variables in a given octant. -/
def octantVars (n : Nat) (level : OctantLevel) (octant : OctantIndex) : List (Var n) :=
  (List.finRange n).filter fun v =>
    if level = 0 then true
    else v.val / (n / (8 ^ level).max 1) = octant % ((8 ^ level).min n)

/-- XOR constraint for a single octant. -/
def octantConstraint (n : Nat) (level : OctantLevel) (octant : OctantIndex) (parity : Bool) : XORConstraint n :=
  { vars := octantVars n level octant, parity := parity }

/-- XOR system for a single octant (both parities). -/
def octantSystems (n : Nat) (level : OctantLevel) (octant : OctantIndex) : List (XORSystem n) :=
  [[octantConstraint n level octant false], [octantConstraint n level octant true]]

/-- All octants at a given level. -/
def octantsAtLevel (n : Nat) (level : OctantLevel) : List (XORSystem n) :=
  (List.range ((8 ^ level).min (n + 1))).flatMap fun octant =>
    octantSystems n level octant

/-- Maximum octant level: log_8(n) levels of subdivision. -/
def maxOctantLevel (n : Nat) : Nat :=
  Nat.log2 n.succ / 3

/-- Morton octant mask family: all octants at all levels. -/
def mortonOctantFamily (n : Nat) : List (XORSystem n) :=
  (List.range (maxOctantLevel n + 1)).flatMap fun level =>
    octantsAtLevel n level

/-- Geometric XOR family: linear masks + Morton octant masks. -/
def geoFamily (n : Nat) : List (XORSystem n) :=
  linearFamily n ++ mortonOctantFamily n

/-- Each octant contributes exactly 2 systems. -/
lemma octantSystems_length (n level octant : Nat) :
    (octantSystems n level octant).length = 2 := rfl

/-- At each level, the number of systems is at most 2 * (n + 1).
    Proof: each of min(8^level, n+1) octants contributes 2 systems. -/
lemma octantsAtLevel_length_bound (n level : Nat) :
    (octantsAtLevel n level).length ≤ 2 * (n + 1) := by
  unfold octantsAtLevel
  rw [List.length_flatMap]
  have hlen : ∀ octant, (octantSystems n level octant).length = 2 := fun _ => rfl
  simp only [hlen]
  rw [List.map_const', List.sum_replicate, List.length_range]
  have hmin : (8 ^ level).min (n + 1) ≤ n + 1 := Nat.min_le_right _ _
  calc (8 ^ level).min (n + 1) * 2
      = 2 * (8 ^ level).min (n + 1) := by ring
    _ ≤ 2 * (n + 1) := by omega

/-- Auxiliary: n + 1 ≤ 2^n for all n. -/
private lemma succ_le_two_pow (n : Nat) : n.succ ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2^n := Nat.one_le_two_pow
    calc n.succ.succ = n.succ + 1 := rfl
      _ ≤ 2 ^ n + 1 := by omega
      _ ≤ 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ n.succ := by omega

/-- Auxiliary: log2(n+1) ≤ n for all n. -/
private lemma log2_succ_le (n : Nat) : Nat.log2 n.succ ≤ n := by
  rw [Nat.log2_eq_log_two]
  have h1 : 1 < 2 := by norm_num
  have h3 : n.succ ≠ 0 := by omega
  have hlt : Nat.log 2 n.succ < n.succ := by
    rw [Nat.log_lt_iff_lt_pow h1 h3]
    have h4 : n.succ.succ ≤ 2^n.succ := succ_le_two_pow n.succ
    calc n.succ < n.succ.succ := by omega
      _ ≤ 2 ^ n.succ := h4
  omega

/-- maxOctantLevel n ≤ n (since log2(n+1)/3 ≤ log2(n+1) ≤ n). -/
lemma maxOctantLevel_le (n : Nat) : maxOctantLevel n ≤ n := by
  unfold maxOctantLevel
  have h1 : Nat.log2 n.succ / 3 ≤ Nat.log2 n.succ := Nat.div_le_self _ _
  have h2 : Nat.log2 n.succ ≤ n := log2_succ_le n
  omega

/-- Auxiliary: flatMap length bound. -/
private lemma flatMap_length_bound' (f : Nat → List (XORSystem n)) (m bound : Nat)
    (hbound : ∀ k < m, (f k).length ≤ bound) :
    ((List.range m).flatMap f).length ≤ m * bound := by
  rw [List.length_flatMap]
  have h : ∀ k ∈ List.range m, (f k).length ≤ bound := by
    intro k hk
    exact hbound k (List.mem_range.mp hk)
  have hsum : (List.map (fun k => (f k).length) (List.range m)).sum ≤
              (List.map (fun _ => bound) (List.range m)).sum := by
    apply List.sum_le_sum
    intro k hk
    exact h k hk
  calc ((List.map (fun k => (f k).length) (List.range m)).sum : Nat)
      ≤ (List.map (fun _ => bound) (List.range m)).sum := hsum
    _ = m * bound := by rw [List.map_const', List.sum_replicate, List.length_range]; ring

/-- Morton octant family has polynomial size O(n²). -/
lemma mortonOctantFamily_size_bound (n : Nat) :
    (mortonOctantFamily n).length ≤ 2 * n.succ ^ 2 := by
  unfold mortonOctantFamily
  have hbound : ∀ level < maxOctantLevel n + 1, (octantsAtLevel n level).length ≤ 2 * (n + 1) :=
    fun level _ => octantsAtLevel_length_bound n level
  have h1 := flatMap_length_bound' (octantsAtLevel n) (maxOctantLevel n + 1) (2 * (n + 1)) hbound
  have h2 : maxOctantLevel n + 1 ≤ n + 1 := by
    have := maxOctantLevel_le n
    omega
  calc (mortonOctantFamily n).length
      = ((List.range (maxOctantLevel n + 1)).flatMap (octantsAtLevel n)).length := rfl
    _ ≤ (maxOctantLevel n + 1) * (2 * (n + 1)) := h1
    _ ≤ (n + 1) * (2 * (n + 1)) := Nat.mul_le_mul_right _ h2
    _ = 2 * (n + 1) ^ 2 := by ring
    _ = 2 * n.succ ^ 2 := rfl

/-- Geometric family has polynomial size O(n²). -/
lemma geoFamily_poly_bound (n : Nat) :
    (geoFamily n).length ≤ 4 * n.succ ^ 2 := by
  unfold geoFamily
  rw [List.length_append]
  have h1 := linearFamily_length_eq n
  have h2 := mortonOctantFamily_size_bound n
  omega

/-- Locality placeholder. -/
def mortonLocality (_n : Nat) (_level : OctantLevel) (_octant : OctantIndex) : Prop := True

/-- Geometric family candidate for isolation. -/
def geoSmallBias : SmallBiasFamily :=
  { 𝓗 := geoFamily }

instance geoSmallBias_poly : HasPolySize geoSmallBias :=
  ⟨⟨4, 2, fun n => geoFamily_poly_bound n⟩⟩

end SAT
end Complexity
end IndisputableMonolith
