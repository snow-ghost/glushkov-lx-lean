import LRX.PacketWindowRoutes
import LRX.WindowFamilyBridge
import LRX.PeriodicRootChildrenRightRoute
import LRX.CycleSelection

/-! A periodic root and finite children in an embedded window yield a full
literal route. All service objects and their filling prices are constructed. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem periodic_window_right_route (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n) (hr : r ≠ 0) (hroot : d r ≠ 0)
    (hstar : PrunedLift.RootStar p d r) (W : Window n b) (hedge : W.offset+b=r.val)
    (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (l : List (State b)) (hcycles : ∀ q ∈ l, q.IsCycle)
    (hdis : l.Pairwise Equiv.Perm.Disjoint) (hparts : ∀ q ∈ l, CyclePart.IsPart q filling)
    (x : ℕ) (hx : x ≤ b) (hpos : ∀ q ∈ l, 0 < FiniteCuts.rightPeak q x)
    (start finish : Fin n) (hstart : start.val+1 ≤ W.offset+x)
    (hfinish : finish.val ≤ (r-1 : Fin n).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1)-
        2*(l.map (fun q => (FiniteCuts.rightPeak q x : ℤ))).sum+2*((r-1 : Fin n).val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  exact packet_window_right_route hn hd hshort r hr hroot (PrunedLift.root_star_packet_cover p d r hstar) W hedge filling hmatch hfinite l hcycles hdis hparts x hx hpos start finish hstart hfinish

#print axioms periodic_window_right_route
end LRX.FiniteWindow
