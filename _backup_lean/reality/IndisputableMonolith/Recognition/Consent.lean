import Mathlib

namespace IndisputableMonolith
namespace Recognition

universe u

/-- Consent window over actions `A` with time bounds and optional revocation. -/
structure ConsentWindow (A : Type u) where
  scope : A → Bool
  tStart : Nat
  tEnd? : Option Nat := none
  revokedAt? : Option Nat := none

namespace ConsentWindow

def activeAt {A} (w : ConsentWindow A) (t : Nat) : Bool :=
  (w.tStart ≤ t) && (match w.tEnd? with | none => True | some te => t ≤ te)
  && (match w.revokedAt? with | none => True | some tr => t < tr)

def permitsAt {A} (w : ConsentWindow A) (t : Nat) (a : A) : Bool :=
  activeAt w t && w.scope a

def revokeAt {A} (w : ConsentWindow A) (r : Nat) : ConsentWindow A :=
  { w with revokedAt? := some (match w.revokedAt? with | none => r | some tr => Nat.min tr r) }

@[simp] lemma revoke_narrows_active {A} (w : ConsentWindow A) (r t : Nat) :
  activeAt (revokeAt w r) t → activeAt w t := by
  unfold activeAt revokeAt
  intro h
  by_cases h1 : w.tEnd? = none
  · cases w.tEnd? <;> simp [h1] at h ⊢
  · cases w.tEnd? <;> simp at h ⊢

@[simp] lemma revoke_narrows_perm {A} (w : ConsentWindow A) (r t : Nat) (a : A) :
  permitsAt (revokeAt w r) t a → permitsAt w t a := by
  unfold permitsAt
  intro h
  have := revoke_narrows_active (w:=w) (r:=r) (t:=t) (by exact And.left h)
  -- conservative boolean reasoning
  have hs : w.scope a = true ∨ w.scope a = false := by
    by_cases hh : w.scope a = true <;> [exact Or.inl hh, exact Or.inr hh]
  cases hs with
  | inl htrue =>
      simp [permitsAt, htrue] at h ⊢
      cases h with
      | intro hact _ =>
          simpa [htrue] using And.intro this rfl
  | inr hfalse =>
      simp [permitsAt, hfalse] at h

end ConsentWindow

/-- A ledger of consent windows. -/
structure ConsentLedger (A : Type u) where
  windows : List (ConsentWindow A)

namespace ConsentLedger

def permits {A} (L : ConsentLedger A) (t : Nat) (a : A) : Bool :=
  L.windows.any (fun w => ConsentWindow.permitsAt w t a)

@[simp] lemma permits_append {A} (L1 L2 : List (ConsentWindow A)) (t : Nat) (a : A) :
  (ConsentLedger.permits { windows := L1 ++ L2 } t a)
  = (ConsentLedger.permits { windows := L1 } t a
     || ConsentLedger.permits { windows := L2 } t a) := by
  unfold ConsentLedger.permits
  simp [List.any_append]

end ConsentLedger

end Recognition
end IndisputableMonolith

