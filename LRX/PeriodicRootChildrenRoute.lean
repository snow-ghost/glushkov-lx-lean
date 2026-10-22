import LRX.RootChildrenAssembly
import LRX.CanonicalServiceFamily
import LRX.OrderedExactRoute

/-! Assemble a periodic root and canonical finite children, with full target
and original affine inversion price. Child services may lie in a smaller window. -/
namespace LRX.RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem periodic_root_children_route (hn : 2 ≤ n) {p selected : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hstar : PrunedLift.RootStar p d 0) (hpart : CyclePart.IsPart selected p) (hfix : selected 0=0)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ))
    (services : List (ExactService n))
    (hdis : services.Pairwise (fun a b => a.service.target.Disjoint b.service.target))
    (hc : CanonicalFamily services)
    (ht : (services.map (fun a => a.service.target)).prod=selected)
    (discount : ℤ)
    (hprice : (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
      (∑ i : Fin n, |(selected.symm i : ℤ)-(i : ℤ)|)-discount)
    (finish : Fin n) (hports : ∀ a ∈ services, a.service.port.val ≤ finish.val) :
    ∃ w : List Letter, eval w=p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-discount+(finish.val : ℤ) := by
  obtain ⟨a,ha,hat,had,har⟩ := CyclePart.selected_part_root_service hn hd hshort hroot hstar hpart hfix hfinite
  exact assemble_periodic_left_word hn hpart hfinite services hdis hc ht discount hprice finish hports a ha hat had har

#print axioms periodic_root_children_route
end LRX.RotationWords
