import LRX.BridgeSequencePositiveLoad

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- The bridge case of (21), including coincident cursor endpoints. -/
theorem joined_bridge_gap_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (i : Fin k) (start finish : Fin n)
    (hxs : (bridgeEndpoints p hc i).1.val ≤ start.val)
    (hxv : start.val < (bridgeEndpoints p hc i).2.val)
    (hys : (bridgeEndpoints p hc i).1.val ≤ finish.val)
    (hyv : finish.val < (bridgeEndpoints p hc i).2.val) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ j, |displacement p.symm j|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+
        ((bridgeEndpoints p hc i).2.val : ℤ)-((bridgeEndpoints p hc i).1.val : ℤ)-3 := by
  let u := (bridgeEndpoints p hc i).1
  let v := (bridgeEndpoints p hc i).2
  have hk : 0 < k := by have := i.isLt; omega
  have hv := (ordered_component_bridge_valid p hc i).1
  have hroots := bridge_endpoints_in_source_packets p hc i
  have hv0 : v ≠ 0 := by
    intro h
    have hv' : u.val < v.val := hv
    rw [h,Fin.val_zero] at hv'
    omega
  have hvpred : (v-1 : Fin n).val=v.val-1 := Fin.val_sub_one_of_ne_zero hv0
  have hxp : start.val ≤ (v-1 : Fin n).val := by rw [hvpred]; change start.val < v.val at hxv; omega
  have hyp : finish.val ≤ (v-1 : Fin n).val := by rw [hvpred]; change finish.val < v.val at hyv; omega
  have hloadL := joined_bridge_port_load p hc i u le_rfl hv
  have hloadR := joined_bridge_port_load p hc i (v-1) (by change u.val ≤ _; rw [hvpred]; change u.val < v.val at hv; omega)
    (by change _ < v.val; rw [hvpred]; change u.val < v.val at hv; omega)
  obtain ⟨wl,hel,hll⟩ := joined_incident_word hn p hc hk u u hroots.1 (Or.inl rfl) start finish
  obtain ⟨wr,her,hlr⟩ := joined_incident_word hn p hc hk v (v-1) hroots.2 (Or.inr (by ring)) start finish
  have hlx := short_move_le_backward_difference start u hxs
  have hly := short_move_le_difference u finish hys
  have hrx := short_move_le_difference start (v-1) hxp
  have hry := short_move_le_backward_difference (v-1) finish hyp
  have hL : ((min (u-start).val (n-(u-start).val)+min (finish-u).val (n-(finish-u).val) : ℕ) : ℤ) ≤
      (start.val : ℤ)+(finish.val : ℤ)-2*(u.val : ℤ) := by
    have hh : min (u-start).val (n-(u-start).val)+min (finish-u).val (n-(finish-u).val)+2*u.val ≤ start.val+finish.val := by omega
    exact_mod_cast (show ((min (u-start).val (n-(u-start).val)+min (finish-u).val (n-(finish-u).val) : ℕ) : ℤ) ≤
      (start.val : ℤ)+(finish.val : ℤ)-2*(u.val : ℤ) by omega)
  have hR : ((min ((v-1)-start).val (n-((v-1)-start).val)+min (finish-(v-1)).val (n-(finish-(v-1)).val) : ℕ) : ℤ) ≤
      2*(v.val : ℤ)-2-(start.val : ℤ)-(finish.val : ℤ) := by
    rw [hvpred] at hrx hry hxp hyp
    omega
  change u.val ≤ start.val at hxs
  change u.val ≤ finish.val at hys
  by_cases hl : (wl.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ j, |displacement p.symm j|)+
      2*(bridgeBudget (componentBridges p hc) : ℤ)+(v.val : ℤ)-(u.val : ℤ)-3
  · exact ⟨wl,hel,hl⟩
  · exact ⟨wr,her,by change (wr.length : ℤ) ≤ _+(v.val : ℤ)-(u.val : ℤ)-3; omega⟩

#print axioms joined_bridge_gap_word
end LRX.FiniteCuts
