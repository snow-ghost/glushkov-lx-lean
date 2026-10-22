import LRX.PacketWindowProfiles
import LRX.PacketPorts
import LRX.GapBoundaryLoad

/-! The full finite-gap word bound for a root packet with arbitrarily many
cycles. Boundary vertices need only belong to the same strong component. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem two_boundary_packet_route (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : W.offset=1)
    (r : Fin n) (hedge : W.offset+b=r.val) (hforward : PrunedLift.Reaches p d 0 r) (hback : PrunedLift.Reaches p d r 0)
    (hwidth : 2*b ≤ n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (start finish : Fin n) (hxy : start.val ≤ finish.val) (hy : finish.val ≤ b) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)+
        min ((start.val : ℤ)+(finish.val : ℤ)-portLoad d 0-FiniteCuts.cycleLeftLoad filling finish.val)
          (2*(b : ℤ)-(start.val : ℤ)-(finish.val : ℤ)-portLoad d (r-1)-FiniteCuts.cycleRightLoad filling start.val) := by
  have hr : r ≠ 0 := by intro h; rw [h,Fin.val_zero,hoff] at hedge; omega
  have hanchor : (r-1 : Fin n).val=b := by
    rw [Fin.val_sub_one_of_ne_zero hr]
    omega
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  have hrootr := PrunedLift.nonzero_reachable hd hshort 0 r hroot hforward
  have hcoverr := PrunedLift.packet_cover_reroot p d 0 r hcover hforward hback
  obtain ⟨wl,hel,hll⟩ := majorized_packet_window_left_line hn hd hm hroot hcover W (by omega) hwidth filling
    hmatch finish.val hy start finish (by omega)
  obtain ⟨wr,her,hlr⟩ := majorized_packet_window_right_line hn hd hm r hr hrootr hcoverr W hedge hwidth filling
    hmatch start.val (by omega) start finish (by omega) (by rw [hanchor]; exact hy)
  rw [hanchor] at hlr
  by_cases h : (start.val : ℤ)+(finish.val : ℤ)-portLoad d 0-FiniteCuts.cycleLeftLoad filling finish.val ≤
      2*(b : ℤ)-(start.val : ℤ)-(finish.val : ℤ)-portLoad d (r-1)-FiniteCuts.cycleRightLoad filling start.val
  · refine ⟨wl,hel,?_⟩
    rw [min_eq_left h]
    linarith
  · refine ⟨wr,her,?_⟩
    rw [min_eq_right (by omega)]
    linarith


theorem finite_gap_packet_word_bound (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : W.offset=1)
    (r : Fin n) (hedge : W.offset+b=r.val) (hforward : PrunedLift.Reaches p d 0 r) (hback : PrunedLift.Reaches p d r 0)
    (hwidth : 2*b ≤ n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (start finish : Fin n) (hxy : start.val ≤ finish.val) (hy : finish.val ≤ b) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-(∑ i : Fin b, |(filling i : ℤ)-(i : ℤ)|)+
        (b*b/2 : ℕ)+(b%2 : ℕ)-portLoad d 0 := by
  obtain ⟨w,he,hl⟩ := two_boundary_packet_route hn hd hm hroot hcover W hoff r hedge hforward hback
    hwidth filling hmatch start finish hxy hy
  have hload := gap_boundary_port_load hd W hoff r hedge filling hmatch
    (fun i => narrow_window_displacement hd (majorized_short hd hm) W hwidth filling hmatch i)
  rw [← hload] at hl
  have hnum := FiniteCuts.finite_cycle_charge_bound filling start.val finish.val hxy hy
  exact ⟨w,he,by omega⟩

#print axioms two_boundary_packet_route
#print axioms finite_gap_packet_word_bound
end LRX.FiniteWindow
