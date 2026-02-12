import Mathlib
import IndisputableMonolith.Ethics.Core

namespace IndisputableMonolith
namespace Ethics
namespace Alignment

structure Morph where
  onPosting : Posting → Posting
  preserves_delta : ∀ p, (onPosting p).delta = p.delta
  preserves_accuracy : ∀ p, (onPosting p).accurate = p.accurate
  preserves_phase : ∀ p, (onPosting p).phase = p.phase

def mapMicro (m : Microcycle) (φ : Morph) : Microcycle :=
  { start := m.start, steps := m.steps.map φ.onPosting }

lemma publish_invariant (m : Microcycle) (φ : Morph) : PublishP (mapMicro m φ) ↔ PublishP m := by
  classical
  unfold mapMicro
  constructor <;> intro h <;> exact h

lemma justice_timely_mapped (m : Microcycle) (φ : Morph) :
  JusticeTimely8 (mapMicro m φ) = JusticeTimely8 m := by
  classical
  unfold JusticeTimely8 mapMicro
  simp [List.length_map, φ.preserves_accuracy, φ.preserves_phase]

lemma temperance_mapped (k : Nat) (m : Microcycle) (φ : Morph) :
  TemperanceCapNat k (mapMicro m φ) = TemperanceCapNat k m := by
  classical
  unfold TemperanceCapNat mapMicro
  simp [List.all_map, φ.preserves_delta]

lemma window_mapped (m : Microcycle) (φ : Morph) :
  ((mapMicro m φ).steps.length ≤ 8) ↔ (m.steps.length ≤ 8) := by
  simp [mapMicro]

lemma unique_keys_mapped (m : Microcycle) (φ : Morph) :
  let keys (m : Microcycle) := m.steps.map (fun p => (p.phase.val, p.delta))
  List.Nodup (keys (mapMicro m φ)) ↔ List.Nodup (keys m) := by
  classical
  unfold mapMicro
  simp [φ.preserves_phase, φ.preserves_delta]

end Alignment
end Ethics
end IndisputableMonolith

