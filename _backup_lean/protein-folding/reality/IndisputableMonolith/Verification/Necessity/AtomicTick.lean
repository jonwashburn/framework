import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Shims.CountableEquiv
import IndisputableMonolith.Verification.Necessity.DiscreteNecessity

namespace IndisputableMonolith
namespace Verification
namespace Necessity
namespace AtomicTickNecessity

open Recognition

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
    simpa [f, hn, hd]
  -- Build the instance from the ℕ-surjection
  exact atomicTickFromNatSurjection M f hfSurj

/-- T2 necessity under zero-parameter (algorithmic) specification of the
    carrier: a discrete skeleton exists surjecting from a countable set,
    hence `AtomicTick`. -/
noncomputable def atomicTickFromZeroParams
  (M : RecognitionStructure)
  (hZero : Necessity.DiscreteNecessity.HasAlgorithmicSpec M.U)
  (hNonempty : Nonempty M.U)
  : Recognition.AtomicTick M :=
by
  classical
  -- Obtain discrete skeleton D and surjection ι : D → M.U
  obtain ⟨D, ι, hSurj, hCount⟩ :=
    Necessity.DiscreteNecessity.zero_params_has_discrete_skeleton (StateSpace:=M.U) hZero
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
  (hZero : Necessity.DiscreteNecessity.HasAlgorithmicSpec M.U)
  (hNonempty : Nonempty M.U)
  : Recognition.AtomicTick M :=
  atomicTickFromZeroParams M hZero hNonempty

end AtomicTickNecessity
end Necessity
end Verification
end IndisputableMonolith
