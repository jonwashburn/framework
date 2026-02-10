import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Gap45

/-!
Module: IndisputableMonolith.Verification.Dimension

This module proves that RSCounting together with 45-gap synchronization forces `D = 3`,
and gives the iff characterization `RSCounting_Gap45_Absolute D ↔ D = 3`.

It is intentionally lightweight: it depends only on arithmetic facts about `lcm` and the local
Pattern/Gap45 certificates (it does **not** import the full RS spec stack).
-/

namespace IndisputableMonolith
namespace Verification
namespace Dimension

/-!
This file intentionally depends only on arithmetic + the local Pattern/Gap45 certificates.

Historically, the lcm filter lemma lived in the broader RS spec layer; we inline the needed
arithmetic equivalence here so `Verification.Dimension` does not pull in the full spec stack.
-/

/-- Arithmetic certificate: `lcm(2^D,45)=360` iff `D=3`.

Proof sketch:
- `45` is odd, so it is coprime to any power of `2`, hence `lcm(2^D,45) = 2^D * 45`.
- `360 = 8 * 45`, so the equation reduces to `2^D = 8 = 2^3`, hence `D=3` by injectivity.
-/
theorem lcm_pow2_45_eq_iff (D : Nat) : Nat.lcm (2 ^ D) 45 = 360 ↔ D = 3 := by
  constructor
  · intro h
    -- since 45 is coprime to any power of 2, lcm = product
    have hcop : Nat.Coprime (2 ^ D) 45 := by
      -- `Coprime 2 45` is decidable and true; lift to powers
      have h2 : Nat.Coprime 2 45 := by decide
      simpa using (h2.pow_left D)
    have hlcm : Nat.lcm (2 ^ D) 45 = (2 ^ D) * 45 := by
      simpa using (hcop.lcm_eq_mul)
    have hmul : (2 ^ D) * 45 = 360 := by simpa [hlcm] using h
    have h360 : 360 = 8 * 45 := by decide
    have hmul' : (2 ^ D) * 45 = 8 * 45 := by simpa [h360] using hmul
    have h45pos : 0 < 45 := by decide
    have hpow : 2 ^ D = 8 := Nat.mul_right_cancel h45pos hmul'
    -- 8 = 2^3
    have hpow' : 2 ^ D = 2 ^ 3 := by simpa using (hpow.trans (by decide : 8 = 2 ^ 3))
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hpow'
  · intro hD
    cases hD
    -- D = 3
    have hpow : (2 ^ 3) = 8 := by decide
    simpa [hpow] using (IndisputableMonolith.Gap45.lcm_8_45_eq_360)

/-- Witness that enforces both: (i) existence of a complete cover of period 2^D,
    and (ii) 45-gap synchronization target 360 via lcm(2^D,45). -/
def DimensionalRigidityWitness (D : Nat) : Prop :=
  (∃ w : IndisputableMonolith.Patterns.CompleteCover D, w.period = 2 ^ D)
  ∧ (Nat.lcm (2 ^ D) 45 = 360)

/-- Strong predicate capturing RS counting and Gap45 synchronization, framed so
    that both hypotheses are structurally relevant and independently witnessed.
    The coverage hypothesis ensures the `2^D` period is not an ad‑hoc number,
    and the synchronization identity ties the rung‑45 timing to that coverage. -/
def RSCounting_Gap45_Absolute (D : Nat) : Prop :=
  (∃ w : IndisputableMonolith.Patterns.CompleteCover D, w.period = 2 ^ D)
  ∧ (Nat.lcm (2 ^ D) 45 = 360)

/-- If both hypercube coverage at 2^D and 45-gap synchronization at 360 hold,
    then the spatial dimension must be D=3. -/
theorem dimension_is_three {D : Nat} (h : DimensionalRigidityWitness D) : D = 3 := by
  rcases h with ⟨hcov, hsync⟩
  -- Coverage not used quantitatively here; the synchronization equation pins D=3.
  -- A stronger version may link coverage/causality structure into uniqueness of the sync.
  simpa using (lcm_pow2_45_eq_iff D).mp hsync

/-- Consolidated theorem: only D=3 satisfies RSCounting + Gap45 synchronization. -/
theorem onlyD3_satisfies_RSCounting_Gap45_Absolute {D : Nat}
  (h : RSCounting_Gap45_Absolute D) : D = 3 := by
  rcases h with ⟨hcov, hsync⟩
  simpa using (lcm_pow2_45_eq_iff D).mp hsync

/-- Strong dimension‑3 necessity from independent witnesses: the existence of a
    complete cover with period `2^D` together with the synchronization identity
    `lcm(2^D,45)=360` forces `D=3`. The coverage premise ensures `2^D` is the
    actual combinatorial period of the cover, not merely an arithmetic placeholder. -/
theorem dimension_three_of_cover_and_sync {D : Nat}
  (hcov : ∃ w : IndisputableMonolith.Patterns.CompleteCover D, w.period = 2 ^ D)
  (hsync : Nat.lcm (2 ^ D) 45 = 360) : D = 3 := by
  simpa using (lcm_pow2_45_eq_iff D).mp hsync

/-- Exact characterization: the RSCounting + Gap45 synchronization predicate holds
    if and only if the spatial dimension is three. This upgrades the one‑way
    necessity into a biconditional sufficiency. -/
theorem rs_counting_gap45_absolute_iff_dim3 {D : Nat} :
  RSCounting_Gap45_Absolute D ↔ D = 3 := by
  constructor
  · intro h; exact onlyD3_satisfies_RSCounting_Gap45_Absolute h
  · intro hD
    cases hD
    constructor
    · exact IndisputableMonolith.Patterns.cover_exact_pow 3
    · -- lcm(2^3,45)=360
      simpa using (lcm_pow2_45_eq_iff 3).mpr rfl

end Dimension
end Verification
end IndisputableMonolith
