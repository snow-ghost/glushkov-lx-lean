import LRX.FiniteIncidentPorts

/-! The finite left/right peak envelopes are attained at active incident ports,
inside the corresponding portion of the interval. -/
namespace LRX.FiniteCuts
variable {b : ℕ}

theorem left_peak_port (p : State b) (y : ℕ) (hy : y ≤ b)
    (hpos : 0 < leftPeak p y) :
    ∃ i : Fin b, p i ≠ i ∧ i.val+1 ≤ y ∧ halfLoad p (i.val+1)=leftPeak p y := by
  have hnon : (Finset.range (y+1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨e, he, hmax⟩ := Finset.exists_mem_eq_sup (Finset.range (y+1)) hnon (halfLoad p)
  have hey : e ≤ y := by have := Finset.mem_range.mp he; omega
  have hp : 0 < halfLoad p e := by change 0 < (Finset.range (y+1)).sup (halfLoad p) at hpos; omega
  obtain ⟨i, hi, hie, hload⟩ := left_incident_port p e (by omega) hp
  exact ⟨i, hi, hie.trans hey, hload.trans hmax.symm⟩

theorem right_peak_port (p : State b) (x : ℕ) (hx : x ≤ b)
    (hpos : 0 < rightPeak p x) :
    ∃ i : Fin b, p i ≠ i ∧ x ≤ i.val ∧ halfLoad p i.val=rightPeak p x := by
  have hnon : (Finset.Icc x b).Nonempty := ⟨x, Finset.mem_Icc.mpr ⟨le_rfl,hx⟩⟩
  obtain ⟨e, he, hmax⟩ := Finset.exists_mem_eq_sup (Finset.Icc x b) hnon (halfLoad p)
  obtain ⟨hxe, heb⟩ := Finset.mem_Icc.mp he
  have hp : 0 < halfLoad p e := by change 0 < (Finset.Icc x b).sup (halfLoad p) at hpos; omega
  obtain ⟨i, hi, hei, hload⟩ := right_incident_port p e heb hp
  exact ⟨i, hi, hxe.trans hei, hload.trans hmax.symm⟩

#print axioms left_peak_port
#print axioms right_peak_port
end LRX.FiniteCuts
