import LRX.TwoArcPacketWord
import LRX.PacketCoordinateSymmetry

/-! The geometric two-arc case is independent of the chosen packet root. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem port_load_recenter (d : Fin n → ℤ) (r t : Fin n) :
    portLoad (localDisplacement d r) t=portLoad d (t+r) := by
  simp only [portLoad,localDisplacement,AffineLift.rotation_power_apply,Fin.cast_val_eq_self,add_assoc]

theorem arc_coordinate_shift (dir : Bool) (r start port : Fin n) :
    arcCoordinate dir (start-r) (port-r)=arcCoordinate dir start port := by
  cases dir <;> simp only [arcCoordinate,Bool.false_eq_true,ite_false,ite_true] <;> ring

theorem admissible_packet_port_recenter (p : State n) (d : Fin n → ℤ) (r port : Fin n)
    (h : AdmissiblePacketPort p d r port) :
    AdmissiblePacketPort (localTarget p 0 r) (localDisplacement d r) 0 (port-r) := by
  obtain ⟨a,ha,hp,hload⟩ := h
  refine ⟨a-r,(core_recenter p d r (a-r)).mpr (by simpa using ha),?_,?_⟩
  · rcases hp with hp | hp
    · exact Or.inl (congrArg (fun i : Fin n => i-r) hp)
    · right
      linear_combination hp
  · simpa only [port_load_recenter,sub_add_cancel] using hload

theorem arbitrary_root_two_arc_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (root : Fin n) (hroot : d root ≠ 0)
    (hcover : PrunedLift.PacketCover p d root) (start finish : Fin n)
    (hboth : ∀ dir : Bool, ∃ port : Fin n, AdmissiblePacketPort p d root port ∧
      (arcCoordinate dir start port).val ≤ (arcCoordinate dir start finish).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  have hd' := recentered_lift 0 root (show AffineLift.IsLift p ((0 : Fin n) : ℤ) d by simpa using hd)
  have hm' := majorized_recenter hm root
  have hr' : localDisplacement d root 0 ≠ 0 := by simpa only [local_displacement_zero] using hroot
  have hc' := packet_cover_recenter p d root hcover
  have hboth' : ∀ dir : Bool, ∃ port : Fin n,
      AdmissiblePacketPort (localTarget p 0 root) (localDisplacement d root) 0 port ∧
      (arcCoordinate dir (start-root) port).val ≤ (arcCoordinate dir (start-root) (finish-root)).val := by
    intro dir
    obtain ⟨port,hgood,hpos⟩ := hboth dir
    exact ⟨port-root,admissible_packet_port_recenter p d root port hgood,
      by simpa only [arc_coordinate_shift] using hpos⟩
  obtain ⟨w,he,hlen⟩ := two_arc_packet_word hn hd' hm' hr' hc' (start-root) (finish-root) hboth'
  exact ⟨w,he.trans (shifted_word_target p root start finish),hlen⟩

#print axioms port_load_recenter
#print axioms arbitrary_root_two_arc_word
end LRX.RotationWords
