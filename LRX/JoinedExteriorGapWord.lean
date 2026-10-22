import LRX.ExternalPortCosts

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n k : ℕ} [NeZero n]

set_option maxHeartbeats 800000 in
/-- The outer-gap case of (21) for the current finite cut. Choosing this gap
maximal is a later geometric step, not an assumption of the route bound. -/
theorem joined_exterior_gap_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (start finish : Fin n)
    (hx : (outerRight p hc).val ≤ start.val ∨ start.val < (outerLeft p hc).val)
    (hy : (outerRight p hc).val ≤ finish.val ∨ finish.val < (outerLeft p hc).val) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+(n : ℤ)+
        ((outerLeft p hc).val : ℤ)-((outerRight p hc).val : ℤ)-1 := by
  let l := outerLeft p hc
  let r := outerRight p hc
  obtain ⟨hlr,hL,hR,hloadL,hloadR⟩ := joined_outer_ports hn p hc hk
  have hxc := external_port_costs hn l r start hlr hx
  have hyc := external_port_costs hn l r finish hlr hy
  obtain ⟨wl,hel,hll⟩ := joined_incident_word hn p hc hk r (r-1) hR (Or.inr (by ring)) start finish
  obtain ⟨wr,her,hlr'⟩ := joined_incident_word hn p hc hk l l hL (Or.inl rfl) start finish
  have hg : ((l-r).val : ℤ)=(n : ℤ)+(l.val : ℤ)-(r.val : ℤ) := by
    have he : (l-r).val+r.val=n+l.val := by
      rw [Fin.coe_sub_iff_lt.mpr (show l < r from hlr)]
      have := r.isLt
      omega
    exact_mod_cast (show ((l-r).val : ℤ)=(n : ℤ)+(l.val : ℤ)-(r.val : ℤ) by omega)
  have hLc : ((min ((r-1)-start).val (n-((r-1)-start).val)+
      min (finish-(r-1)).val (n-(finish-(r-1)).val) : ℕ) : ℤ) ≤
      ((start-r).val : ℤ)+((finish-r).val : ℤ)+2 := by
    have ha := hxc.1
    have hb := hyc.2.1
    omega
  have hRc : ((min (l-start).val (n-(l-start).val)+min (finish-l).val (n-(finish-l).val) : ℕ) : ℤ) ≤
      2*((l-r).val : ℤ)-((start-r).val : ℤ)-((finish-r).val : ℤ) := by
    have ha := hxc.2.2.1
    have hb := hyc.2.2.2
    have hxa : (start-r).val ≤ (l-r).val := by
      rcases hx with hx | hx
      · rw [Fin.sub_val_of_le hx,Fin.coe_sub_iff_lt.mpr (show l < r from hlr)]
        have := start.isLt
        omega
      · rw [Fin.coe_sub_iff_lt.mpr (show start < r by change start.val < r.val; change start.val < l.val at hx; change l.val < r.val at hlr; omega),
          Fin.coe_sub_iff_lt.mpr (show l < r from hlr)]
        omega
    have hya : (finish-r).val ≤ (l-r).val := by
      rcases hy with hy | hy
      · rw [Fin.sub_val_of_le hy,Fin.coe_sub_iff_lt.mpr (show l < r from hlr)]
        have := finish.isLt
        omega
      · rw [Fin.coe_sub_iff_lt.mpr (show finish < r by change finish.val < r.val; change finish.val < l.val at hy; change l.val < r.val at hlr; omega),
          Fin.coe_sub_iff_lt.mpr (show l < r from hlr)]
        omega
    omega
  change 2 ≤ portLoad (displacement (joinedComponents p hc).symm) l at hloadL
  change 2 ≤ portLoad (displacement (joinedComponents p hc).symm) (r-1) at hloadR
  by_cases hl : (wl.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
      2*(bridgeBudget (componentBridges p hc) : ℤ)+(n : ℤ)+(l.val : ℤ)-(r.val : ℤ)-1
  · exact ⟨wl,hel,hl⟩
  · exact ⟨wr,her,by change (wr.length : ℤ) ≤ _+(n : ℤ)+(l.val : ℤ)-(r.val : ℤ)-1; omega⟩

#print axioms joined_exterior_gap_word
end LRX.FiniteCuts
