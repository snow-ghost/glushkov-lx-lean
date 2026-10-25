import LRX.InversionSet
import Mathlib

/-! Exact paid length after affine pair deletion, and its application to the
service of all cycles reachable from the chosen root. -/
namespace LRX.LiftedModel
variable {n : ℕ} [NeZero n]

/-- Full affine deletion theorem: preserve the entire lifted endpoint and every
L/R letter, with exactly the affine inversion count remaining as X. -/
theorem affine_reduction_exact (hn : 2 ≤ n) (w : List Letter) :
    ∃ v : List Letter,
      run v (initial (n := n))=run w (initial (n := n)) ∧
      eval v=eval (n := n) w ∧
      rotationLetters v=rotationLetters w ∧
      BufferProgram.exchanges v=inversionCount (run w (initial (n := n))).position ∧
      v.length=inversionCount (run w (initial (n := n))).position+BufferProgram.rotations w ∧
      v.Sublist w := by
  obtain ⟨v, he, hv, hr, hrot, hnd, _, hsub⟩ := affine_reduced_word hn w
  have hx := reduced_exchange_count hn v hnd
  rw [he] at hx
  refine ⟨v, he, hv, hr, hx, ?_, hsub⟩
  rw [length_eq_event_rotation v (initial (n := n)), event_count_length, hx, hrot]

#print axioms affine_reduction_exact
end LRX.LiftedModel

namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]


end LRX.BufferProgram
