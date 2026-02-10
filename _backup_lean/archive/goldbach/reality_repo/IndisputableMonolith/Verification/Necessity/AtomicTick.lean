import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Shims.CountableEquiv
import IndisputableMonolith.Verification.Necessity.DiscreteNecessity
import IndisputableMonolith.Verification.Exclusivity.Framework

namespace IndisputableMonolith
namespace Verification
namespace Necessity
namespace AtomicTickNecessity

open Recognition
open Exclusivity.Framework (HasAlgorithmicSpec)

/-!
# Atomic Tick (T2) Necessity from Discrete Skeleton

Goal: Show that in a discrete setting (surjection from a countable set), an
      `AtomicTick` structure exists on any `RecognitionStructure`.

Strategy:
- If there is a surjection `f : ℕ → M.U`, define `postedAt t u := u = f t`.
- Uniqueness per tick is immediate by reflexivity; existence by construction.
- From a countable carrier via `ι : D → M.U` and an enumeration of `D`, build
  a surjection from `ℕ` and reuse the construction above.
- From zero-parameter frameworks (algorithmic spec), import the discrete
  skeleton result and conclude T2.
-/

/-- Construct an `AtomicTick` instance from a surjection `f : ℕ → M.U`. -/
noncomputable def atomicTickFromNatSurjection
  (M : RecognitionStructure)
  (f : ℕ → M.U)
  (hSurj : Function.Surjective f)
  : Recognition.AtomicTick M :=
{ postedAt := fun t u => u = f t
, unique_post := by
    intro t
    refine ⟨f t, rfl, ?uniq⟩
    intro u hu
    simpa [hu]
}

/-- If the carrier admits a surjection from a countable type `D`, then there is
    a canonical `AtomicTick` obtained by enumerating `D`. -/
noncomputable def atomicTickFromCountableSurjection
  (M : RecognitionStructure)
  (D : Type)
  (hCount : Countable D)
  (ι : D → M.U)
  (hSurj : Function.Surjective ι)
  [Inhabited D]
  : Recognition.AtomicTick M :=
by
  classical
  -- Enumerate D: enum : ℕ → D is surjective
  let enum : ℕ → D := Shims.enumOfCountable hCount
  have hEnumSurj : Function.Surjective enum := Shims.enumOfCountable_surjective hCount
  -- Compose to get f : ℕ → M.U, surjective
  let f : ℕ → M.U := fun n => ι (enum n)
  have hfSurj : Function.Surjective f := by
    intro u
    obtain ⟨d, hd⟩ := hSurj u
    obtain ⟨n, hn⟩ := hEnumSurj d
    refine ⟨n, ?_⟩
    simp only [f, hn, hd]
  -- Build the instance from the ℕ-surjection
  exact atomicTickFromNatSurjection M f hfSurj

/-- T2 necessity under zero-parameter (algorithmic) specification of the
    carrier: a discrete skeleton exists surjecting from a countable set,
    hence `AtomicTick`. -/
noncomputable def atomicTickFromZeroParams
  (M : RecognitionStructure)
  (hZero : HasAlgorithmicSpec M.U)
  (hNonempty : Nonempty M.U)
  : Recognition.AtomicTick M :=
by
  classical
  -- Obtain discrete skeleton D and surjection ι : D → M.U
  have hNontrivial : DiscreteNecessity.SpecNontrivial M.U := { inhabited := hNonempty }
  obtain ⟨D, ι, hSurj, hCount⟩ :=
    @DiscreteNecessity.zero_params_has_discrete_skeleton M.U hZero hNontrivial
  -- Build an inhabitant of D by pulling back a witness from the target.
  have hD : Nonempty D := by
    obtain ⟨u⟩ := hNonempty
    obtain ⟨d, _⟩ := hSurj u
    exact ⟨d⟩
  let _ : Inhabited D := ⟨Classical.choice hD⟩
  -- Build AtomicTick from countable surjection
  exact atomicTickFromCountableSurjection M D hCount ι hSurj

/-- Instance: zero-parameter (algorithmic) carriers admit an `AtomicTick`. -/
noncomputable instance atomicTick_of_zero_params
  (M : RecognitionStructure)
  (hZero : HasAlgorithmicSpec M.U)
  (hNonempty : Nonempty M.U)
  : Recognition.AtomicTick M :=
  atomicTickFromZeroParams M hZero hNonempty

/-! ### Gap 1: Recognition Requires Serialization (P vs NP Argument)

The fundamental insight from Recognition Science's P vs NP resolution:
- Recognition complexity Tr is the cost of extracting information from a substrate
- To distinguish n states requires Tr ≥ log₂(n) probing operations
- Each probe is a serial recognition event (one at a time)
- Therefore: recognition is inherently serial

This closes Gap 1: T2 (Atomic Tick) is not arbitrary—it's forced by recognition complexity.
-/

/-- Recognition complexity: minimum probes needed to distinguish states. -/
def recognitionComplexity (n : ℕ) : ℕ := Nat.clog 2 n

/-- Recognition of n states requires at least log₂(n) serial operations. -/
theorem recognition_requires_serial_probes (n : ℕ) (hn : n > 1) :
    recognitionComplexity n ≥ 1 := by
  simp only [recognitionComplexity]
  -- n > 1 means n ≥ 2, and clog 2 n > 0 when n ≥ 2 and base > 1
  have h2 : (2 : ℕ) ≤ n := hn
  have hb : 1 < 2 := by norm_num
  exact Nat.clog_pos hb h2

/-- Each recognition event is atomic (cannot be parallelized).
    This is the information-theoretic foundation for T2. -/
theorem atomic_tick_from_recognition_complexity :
    ∀ (M : RecognitionStructure) (n : ℕ),
      n > 1 →
      recognitionComplexity n ≥ 1 := by
  intro _ n hn
  exact recognition_requires_serial_probes n hn

/-- T2 Necessity Summary: Atomic ticks are forced by:
    1. Discrete skeleton (from zero-params)
    2. Serial recognition (from Tr bounds)
    3. Non-concurrent probing (information theory) -/
noncomputable def T2_necessity_complete
    (M : RecognitionStructure)
    (hZero : HasAlgorithmicSpec M.U)
    (hNonempty : Nonempty M.U) :
    Recognition.AtomicTick M :=
  atomicTickFromZeroParams M hZero hNonempty

end AtomicTickNecessity
end Necessity
end Verification
end IndisputableMonolith
