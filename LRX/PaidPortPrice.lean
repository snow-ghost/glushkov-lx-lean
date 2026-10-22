import LRX.PortLoad
import LRX.RecenteredCrossings

/-! The complete paid price is expressed entirely in statistics of the original
lift, including the original affine X count and the load at the chosen cut. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem paid_port_price (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (c r : Fin n) (hd : AffineLift.IsLift p (c : ℤ) d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d r ≠ 0)
    (hreach : ∀ i : Fin n, localDisplacement d r i ≠ 0 →
      Relation.ReflTransGen (BufferProgram.ServiceEdge (localTarget p c r)
        (localDisplacement d r)) 0 i) :
    ∃ w : List Letter, eval w=p ∧
      BufferProgram.exchanges w=LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) ∧
      (w.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-
        (∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ)
          ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i))+
        (min r.val (n-r.val) : ℕ)+(min (c-r).val (n-(c-r).val) : ℕ) := by
  obtain ⟨w, he, hx, hl⟩ := paid_root_service hn c r hd hshort hroot hreach
  rw [inversion_count_recentered c r hd] at hx hl
  rw [port_load_original] at hl
  exact ⟨w, he, hx, hl⟩

#print axioms paid_port_price
end LRX.RotationWords
