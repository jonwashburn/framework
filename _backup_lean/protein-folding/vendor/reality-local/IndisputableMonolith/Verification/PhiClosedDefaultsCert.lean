import Mathlib
import IndisputableMonolith.RH.RS.Spec

/-!
# Phi-Closed Defaults Certificate (no hidden constants beyond φ)

This certificate packages the fact that the **spec-level default dimensionless values**
are built from `φ` using field operations only:

- `alphaDefault φ` is `PhiClosed φ`
- every element of `massRatiosDefault φ` is `PhiClosed φ`
- every element of `mixingAnglesDefault φ` is `PhiClosed φ`
- `g2Default φ` is `PhiClosed φ`

This is a non-circularity guard: it prevents “defaults” from smuggling in extra
constants beyond `φ` under opaque names.
-/

namespace IndisputableMonolith
namespace Verification
namespace PhiClosedDefaults

open IndisputableMonolith.RH

structure PhiClosedDefaultsCert where
  deriving Repr

@[simp] def PhiClosedDefaultsCert.verified (_c : PhiClosedDefaultsCert) : Prop :=
  ∀ φ : ℝ,
    (RS.PhiClosed φ (RS.alphaDefault φ))
    ∧ (∀ r ∈ RS.massRatiosDefault φ, RS.PhiClosed φ r)
    ∧ (∀ θ ∈ RS.mixingAnglesDefault φ, RS.PhiClosed φ θ)
    ∧ (RS.PhiClosed φ (RS.g2Default φ))

@[simp] theorem PhiClosedDefaultsCert.verified_any (c : PhiClosedDefaultsCert) :
    PhiClosedDefaultsCert.verified c := by
  intro φ
  refine And.intro (RS.phiClosed_alphaDefault φ) (And.intro ?_ (And.intro ?_ ?_))
  · intro r hr
    simp only [RS.massRatiosDefault, List.mem_cons, List.mem_singleton] at hr
    rcases hr with rfl | rfl | h
    · exact RS.PhiClosed.self _
    · exact RS.phiClosed_one_div_pow _ 2
    · contradiction
  · intro θ hθ
    simp only [RS.mixingAnglesDefault, List.mem_cons, List.mem_singleton] at hθ
    rcases hθ with rfl | h
    · exact RS.phiClosed_one_div _
    · contradiction
  · -- g2Default φ = 1 / φ^5
    exact RS.phiClosed_one_div_pow φ 5

end PhiClosedDefaults
end Verification
end IndisputableMonolith
