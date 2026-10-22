import LRX.InversionSet
import LRX.ReachableService

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

/-- The reachable service now has a proved total price C(F)+Delta-lambda(0),
including its X count. Sharp comparison with n.choose 2 is still separate. -/
theorem reachable_service_price (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hroot : (p⁻¹) 0 ≠ 0)
    (hreach : ∀ i : Fin n, d i ≠ 0 → Relation.ReflTransGen (ServiceEdge p d) 0 i) :
    ∃ w : List Letter,
      eval w=p ∧
      (LiftedModel.run w (LiftedModel.initial (n := n))).cursor=0 ∧
      (∀ i, (LiftedModel.run w (LiftedModel.initial (n := n))).position i=(i : ℤ)+d i) ∧
      exchanges w=LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) ∧
      (w.length : ℤ)=(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-
        ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (i : ℤ) ((i : ℤ)+d i) := by
  obtain ⟨raw, hp, hc, hpos, hr⟩ := reachable_lift_service hn hd hroot hreach
  obtain ⟨w, he, hw, _, hx, hlen, _⟩ := LiftedModel.affine_reduction_exact hn raw
  have hfun : (LiftedModel.run raw (LiftedModel.initial (n := n))).position=
      fun i : Fin n => (i : ℤ)+d i := funext hpos
  rw [hfun] at hx hlen
  refine ⟨w, hw.trans hp, ?_, ?_, hx, ?_⟩
  · rw [he]; exact hc
  · intro i; rw [he]; exact hpos i
  · rw [hlen, Nat.cast_add, hr]
    ring

#print axioms reachable_service_price
end LRX.BufferProgram
