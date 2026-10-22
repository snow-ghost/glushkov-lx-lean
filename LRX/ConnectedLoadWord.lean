import LRX.LoadComponentService
import LRX.ComponentLoad
import LRX.ReducedRouteFrom

/-! Paid words for a single connected load support and for individual
components cut out of an arbitrary lift. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem packet_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (r : Fin n) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r) (start finish : Fin n) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ)=(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-RotationWords.portLoad d r+
        (min (r-start).val (n-(r-start).val) : ℤ)+
        (min (finish-r).val (n-(finish-r).val) : ℤ) := by
  obtain ⟨a,ha,ht,hdisp,hprice⟩ := RotationWords.packet_exact_service hn hd hshort r hroot hcover
  obtain ⟨w,he,hlen⟩ := RotationWords.reduced_route_from hn hd [a] (by simp)
    (by simp [ht]) (by intro i; simp [hdisp]) start finish
  refine ⟨w,he,?_⟩
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
    RotationWords.walkCost,ha] at hlen
  have hz := congrArg (fun k : ℕ => (k : ℤ)) hlen
  push_cast at hz
  omega

theorem connected_load_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (initial : Active p)
    (hconn : ∀ b : Active p, LoadPath d initial.val b.val) (start finish : Fin n) :
    ∃ r : Fin n, ∃ w : List Letter,
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ)=(LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-RotationWords.portLoad d r+
        (min (r-start).val (n-(r-start).val) : ℤ)+
        (min (finish-r).val (n-(finish-r).val) : ℤ) := by
  obtain ⟨root,hcover⟩ := connected_load_packet hd hshort initial hconn
  have hroot : d root.val ≠ 0 := by
    intro hz
    have hr := AffineLift.lift_residue hd root.val
    simp only [hz,Int.cast_zero,add_zero] at hr
    exact root.property hr.symm
  exact ⟨root.val,packet_word hn hd hshort root.val hroot hcover start finish⟩

theorem component_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (cut : Fin n) (hz : RotationWords.portLoad d cut=0) (initial : Active p) (start finish : Fin n) :
    ∃ r : Fin n, ∃ w : List Letter, r ∈ component d initial.val ∧
      eval w=(RotationWords.rotation start)⁻¹*
        PrunedLift.permutation p (component d initial.val) (component_invariant hd initial.val)*
        RotationWords.rotation finish ∧
      (w.length : ℤ)=(LiftedModel.inversionCount
        (fun i : Fin n => (i : ℤ)+PrunedLift.displacement (component d initial.val) d i) : ℤ)+
        (∑ i : Fin n, |PrunedLift.displacement (component d initial.val) d i|)-RotationWords.portLoad d r+
        (min (r-start).val (n-(r-start).val) : ℤ)+
        (min (finish-r).val (n-(finish-r).val) : ℤ) := by
  obtain ⟨r,a,hr,ha,ht,hdisp,hprice⟩ := component_exact_service hn hd hshort cut hz initial
  have hlocal := PrunedLift.is_lift hd (component d initial.val) (component_invariant hd initial.val)
    (component_balanced hd cut hz initial.val)
  obtain ⟨w,he,hlen⟩ := RotationWords.reduced_route_from hn hlocal [a] (by simp)
    (by simp [ht]) (by intro i; simp [hdisp]) start finish
  refine ⟨r,w,hr,he,?_⟩
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
    RotationWords.walkCost,ha] at hlen
  rw [component_port_load d initial.val r hr] at hprice
  have hz := congrArg (fun k : ℕ => (k : ℤ)) hlen
  push_cast at hz
  omega

#print axioms connected_load_word
#print axioms component_word
end LRX.CycleFootprint
