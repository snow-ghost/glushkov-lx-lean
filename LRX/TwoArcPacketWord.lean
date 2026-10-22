import LRX.ArcCycleSelection
import LRX.PacketIncidentSharpWord

/-! Geometric two-arc routing: positive incident packet ports on the two
arcs suffice. Service families and their total saving are constructed. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def AdmissiblePacketPort (p : State n) (d : Fin n → ℤ) (root port : Fin n) : Prop :=
  ∃ r, PrunedLift.InCore p d root r ∧ (port=r ∨ port+1=r) ∧ 0 < portLoad d port

theorem admissible_packet_cursor_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (cursor : Fin n)
    (hgood : AdmissiblePacketPort p d 0 cursor) :
    ∃ w : List Letter, eval w=(rotation cursor)⁻¹*p*rotation cursor ∧ w.length ≤ n.choose 2 := by
  obtain ⟨r,hr,hp,hpos⟩ := hgood
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  obtain ⟨services,hdis,ht,hdisp,hports,hrot⟩ := ZeroGap.arc_packet_service_family hn hd hshort hroot hcover
    true cursor cursor [] (by simp) (by simp) (by simp) r cursor hr hp hpos (by simp [arcCoordinate])
  obtain ⟨w,he,hlen⟩ := circular_reduced_route hn hd true cursor cursor services hdis ht hdisp hports
  have hbudget := FiniteGaps.base_word_budget hd hm
  simp only [arcCoordinate,ite_true,sub_self,Fin.val_zero,Nat.add_zero] at hlen
  simp only [List.length_nil,Nat.cast_zero,mul_zero,sub_zero] at hrot
  exact ⟨w,he,by omega⟩

theorem two_arc_packet_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (start finish : Fin n)
    (hboth : ∀ dir : Bool, ∃ port : Fin n, AdmissiblePacketPort p d 0 port ∧
      (arcCoordinate dir start port).val ≤ (arcCoordinate dir start finish).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  classical
  by_cases hne : start=finish
  · subst finish
    obtain ⟨port,hgood,hport⟩ := hboth true
    have he : port=start := by
      apply sub_eq_zero.mp
      apply Fin.ext
      simp only [arcCoordinate,ite_true,sub_self,Fin.val_zero] at hport
      simpa only [Fin.val_zero] using (show (port-start).val=0 by omega)
    subst port
    exact admissible_packet_cursor_word hn hd hm hroot hcover start hgood
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := FiniteWindow.majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  obtain ⟨cycles,hcycles,hout,hcycleports,hcount⟩ := ZeroGap.arc_cycle_partition p d start finish hne
  have hfamilies : ∀ dir : Bool, ∃ all : List (ExactService n),
      all.Pairwise (fun a b => a.service.target.Disjoint b.service.target) ∧
      (all.map (fun a => a.service.target)).prod=p ∧
      (∀ i, (all.map (fun a => a.displacement i)).sum=d i) ∧
      (∀ a ∈ all, (arcCoordinate dir start a.service.port).val ≤ (arcCoordinate dir start finish).val) ∧
      ((all.map (fun a => BufferProgram.rotations a.service.word)).sum : ℤ) ≤
        (∑ i : Fin n, |d i|)-2*((cycles dir).length : ℤ)-2 := by
    intro dir
    obtain ⟨port,⟨r,hr,hp,hpos⟩,hport⟩ := hboth dir
    exact ZeroGap.arc_packet_service_family hn hd hshort hroot hcover dir start finish
      (cycles dir) (hcycles dir) (hout dir) (hcycleports dir) r port hr hp hpos hport
  choose services hdis ht hdisp hports hrot using hfamilies
  apply two_arc_service_word hn hd hm 0 start finish hne services hdis ht hdisp hports
  have hleft := hrot true
  have hright := hrot false
  omega

#print axioms admissible_packet_cursor_word
#print axioms two_arc_packet_word
end LRX.RotationWords
