import LRX.PacketGapMass

/-! Every visited gap in the actual partition has strictly less than half
of the physical circle between its boundary vertices. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem core_copy_outside_partition_gap (p : State n) (d : Fin n → ℤ) (a : Fin n)
    (z : ℤ) (hz : (z : Fin n) ∈ PrunedLift.core p d 0) :
    z ≤ (a : ℤ) ∨ (next (PrunedLift.core p d 0) a : ℤ) ≤ z := by
  by_contra h
  push Not at h
  have hN := next_le (PrunedLift.core p d 0) a
  have hnon : (0 : ℤ) ≤ z := by
    have ha : (0 : ℤ) ≤ a := by positivity
    omega
  have hlt : z < (n : ℤ) := by omega
  have he : ((z : Fin n) : ℤ)=z := by simp [Int.emod_eq_of_lt hnon hlt,hnon]
  have hgap : (z : Fin n) ∈ positions (PrunedLift.core p d 0) a := by
    apply (mem_positions _ _ _).mpr
    constructor <;> omega
  exact gap_avoids_marks _ a _ hgap hz

theorem internal_size_bound {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (a : Fin n)
    (ha : Internal p d a) : 2*(size (PrunedLift.core p d 0) a+1) < n := by
  obtain ⟨s,x,hs,hx,k,hlo,hhi⟩ := ha
  have hscore := (PrunedLift.mem_core p d 0 s).mp hs
  have htcore := PrunedLift.in_core_same_cycle p d 0 hscore (Equiv.Perm.SameCycle.refl _ _).apply_right
  have hs' : (((s : ℤ)-k*(n : ℤ) : ℤ) : Fin n)=s := by simp
  have ht' : (((s : ℤ)+d s-k*(n : ℤ) : ℤ) : Fin n)=p.symm s := by
    calc
      _ = (((s : ℤ)+d s : ℤ) : Fin n) := by simp
      _ = p.symm s := by simpa using AffineLift.lift_residue hd s
  have hstart := core_copy_outside_partition_gap p d a ((s : ℤ)-k*(n : ℤ)) (by simpa only [hs'] using hs)
  have hfinish := core_copy_outside_partition_gap p d a ((s : ℤ)+d s-k*(n : ℤ))
    (by simpa only [ht'] using (PrunedLift.mem_core p d 0 (p.symm s)).mpr htcore)
  have hx' := (mem_positions (PrunedLift.core p d 0) a x).mp hx
  have habs := le_abs_self (d s)
  have habs' := neg_le_abs (d s)
  have hshort := FiniteWindow.majorized_short hd hm s
  have hnext := lt_next (PrunedLift.core p d 0) a
  unfold size
  rcases hstart with hstart | hstart <;> rcases hfinish with hfinish | hfinish <;> omega

theorem internal_sizes_total (p : State n) (d : Fin n → ℤ) :
    (∑ a ∈ internalStarts p d, size (PrunedLift.core p d 0) a) ≤ n-(PrunedLift.core p d 0).card := by
  classical
  have h : (∑ a ∈ internalStarts p d, size (PrunedLift.core p d 0) a) ≤
      ∑ a ∈ PrunedLift.core p d 0, size (PrunedLift.core p d 0) a :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  rw [sum_gap_sizes _ (core_zero p d)] at h
  exact h

#print axioms internal_size_bound
#print axioms internal_sizes_total
end LRX.FiniteGaps
