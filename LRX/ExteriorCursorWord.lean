import LRX.IncidentPacketWord
import LRX.ExteriorBoundaryPorts
import LRX.TurningRoute
import LRX.PacketPorts
import LRX.PacketCoreBalance

namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem short_neg_one_costs (hn : 2 ≤ n) (i : Fin n) (hi : i.val+1<n) :
    min ((-1 : Fin n)-i).val (n-((-1 : Fin n)-i).val) ≤ i.val+1 ∧
    min (i-(-1 : Fin n)).val (n-(i-(-1 : Fin n)).val) ≤ i.val+1 := by
  have hone : (1 : Fin n).val=1 := by
    change (1 : ℕ)%n=1
    exact Nat.mod_eq_of_lt (by omega)
  have hne : (1 : Fin n) ≠ 0 := by intro h; have := congrArg Fin.val h; simp only [hone,Fin.val_zero] at this; omega
  have hneg : (-1 : Fin n).val=n-1 := by rw [Fin.val_neg,if_neg hne,hone]
  have hle : i.val ≤ (-1 : Fin n).val := by omega
  have hlt : i < (-1 : Fin n) := by change i.val < (-1 : Fin n).val; omega
  constructor
  · have h := min_le_right ((-1 : Fin n)-i).val (n-((-1 : Fin n)-i).val)
    rw [Fin.sub_val_of_le hle,hneg] at h ⊢
    omega
  · have h := min_le_left (i-(-1 : Fin n)).val (n-(i-(-1 : Fin n)).val)
    rw [Fin.coe_sub_iff_lt.mpr hlt,hneg] at h ⊢
    omega

theorem exterior_cursor_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (r : Fin n) (hr : PrunedLift.InCore p d 0 r)
    (b : ℕ) (hb : r.val=b+1) (hz : portLoad d 0=0) (hzr : portLoad d (r-1)=0)
    (start finish : Fin n) (hx : start.val ≤ b) (hy : finish.val ≤ b) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤ (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)+(b : ℤ) := by
  have hdr := PrunedLift.nonzero_reachable hd hshort 0 r hroot hr.1
  have hc := PrunedLift.packet_cover_reroot p d 0 r hcover hr.1 hr.2
  have hleftload : 2 ≤ portLoad d (-1) := by simpa using zero_right_load_left_discount hd 0 hroot hz
  have hrightload := zero_left_load_right_discount hd r hdr hzr
  obtain ⟨left,hle,hll⟩ := incident_packet_word hn hd hshort 0 (-1) hroot hcover (Or.inr (by ring)) start finish
  obtain ⟨right,hre,hrl⟩ := incident_packet_word hn hd hshort r r hdr hc (Or.inl rfl) start finish
  have hxs := short_neg_one_costs hn start (by have := r.isLt; omega)
  have hys := short_neg_one_costs hn finish (by have := r.isLt; omega)
  have hxr := short_move_le_difference start r (by omega)
  have hyr := short_move_le_backward_difference r finish (by omega)
  have hxsZ : ((min ((-1 : Fin n)-start).val (n-((-1 : Fin n)-start).val) : ℕ) : ℤ) ≤ (start : ℤ)+1 := by
    exact_mod_cast hxs.1
  have hysZ : ((min (finish-(-1 : Fin n)).val (n-(finish-(-1 : Fin n)).val) : ℕ) : ℤ) ≤ (finish : ℤ)+1 := by
    exact_mod_cast hys.2
  have hxrZ : ((min (r-start).val (n-(r-start).val) : ℕ) : ℤ)+(start : ℤ) ≤ (r : ℤ) := by
    exact_mod_cast (show min (r-start).val (n-(r-start).val)+start.val ≤ r.val by omega)
  have hyrZ : ((min (finish-r).val (n-(finish-r).val) : ℕ) : ℤ)+(finish : ℤ) ≤ (r : ℤ) := by
    exact_mod_cast (show min (finish-r).val (n-(finish-r).val)+finish.val ≤ r.val by omega)
  have hbZ : (r : ℤ)=(b : ℤ)+1 := by exact_mod_cast hb
  have hL : (left.length : ℤ) ≤
      (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+(∑ i : Fin n, |d i|)+
      (start : ℤ)+(finish : ℤ) := by
    linarith only [hll,hleftload,hxsZ,hysZ]
  have hR : (right.length : ℤ) ≤
      (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+(∑ i : Fin n, |d i|)+
      2*(b : ℤ)-(start : ℤ)-(finish : ℤ) := by
    linarith only [hrl,hrightload,hxrZ,hyrZ,hbZ]
  by_cases hl : (left.length : ℤ) ≤
      (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+(∑ i : Fin n, |d i|)+(b : ℤ)
  · exact ⟨left,hle,hl⟩
  · exact ⟨right,hre,by linarith only [hL,hR,hl]⟩

#print axioms exterior_cursor_word
end LRX.RotationWords
