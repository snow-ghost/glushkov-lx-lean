import LRX.PacketWindowRoutes
import LRX.WindowFamilyBridge
import LRX.PeriodicRootChildrenRoute
import LRX.CycleSelection

/-! A periodic root and finite children in an embedded window yield a full
literal route. All service objects and their filling prices are constructed. -/
namespace LRX.FiniteWindow
open scoped BigOperators
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem periodic_window_left_route (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hstar : PrunedLift.RootStar p d 0) (W : Window n b) (hoff : 0 < W.offset)
    (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (l : List (State b)) (hcycles : ∀ q ∈ l, q.IsCycle)
    (hdis : l.Pairwise Equiv.Perm.Disjoint) (hparts : ∀ q ∈ l, CyclePart.IsPart q filling)
    (y : ℕ) (hy : y ≤ b) (hpos : ∀ q ∈ l, 0 < FiniteCuts.leftPeak q y)
    (finish : Fin n) (hfinish : W.offset+y ≤ finish.val+1) :
    ∃ w : List Letter, eval w=p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-
        2*(l.map (fun q => (FiniteCuts.leftPeak q y : ℤ))).sum+(finish.val : ℤ) := by
  exact packet_window_left_route hn hd hshort hroot (PrunedLift.root_star_packet_cover p d 0 hstar) W hoff filling hmatch hfinite l hcycles hdis hparts y hy hpos finish hfinish

#print axioms periodic_window_left_route
end LRX.FiniteWindow
