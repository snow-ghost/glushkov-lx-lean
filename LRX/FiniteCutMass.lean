import LRX.FiniteCuts

/-! Double counting actual finite cut crossings gives the exact footrule. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

theorem forward_as_sum (p : State b) (e : ℕ) :
    halfLoad p e=∑ i : Fin b, if i.val < e ∧ e ≤ (p i).val then 1 else 0 := by
  have hs : forward p e=Finset.univ.filter (fun i : Fin b => i.val < e ∧ e ≤ (p i).val) := by
    ext i; simp
  rw [halfLoad, hs]
  simpa using (Finset.sum_boole (R := ℕ)
    (fun i : Fin b => i.val < e ∧ e ≤ (p i).val) Finset.univ).symm

theorem backward_as_sum (p : State b) (e : ℕ) :
    (backward p e).card=∑ i : Fin b, if (p i).val < e ∧ e ≤ i.val then 1 else 0 := by
  have hs : backward p e=Finset.univ.filter (fun i : Fin b => (p i).val < e ∧ e ≤ i.val) := by
    ext i; simp
  rw [hs]
  simpa using (Finset.sum_boole (R := ℕ)
    (fun i : Fin b => (p i).val < e ∧ e ≤ i.val) Finset.univ).symm

theorem crossing_cut_count (a z : Fin b) :
    (∑ e ∈ Finset.range (b+1), if a.val < e ∧ e ≤ z.val then (1 : ℕ) else 0)=z.val-a.val := by
  rw [Finset.sum_boole]
  have hs : (Finset.range (b+1)).filter (fun e => a.val < e ∧ e ≤ z.val)=
      Finset.Ioc a.val z.val := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    have hz := z.isLt
    omega
  rw [hs, Nat.card_Ioc]
  simp

theorem forward_cut_sum (p : State b) :
    (∑ e ∈ Finset.range (b+1), halfLoad p e)=∑ i : Fin b, ((p i).val-i.val) := by
  simp_rw [forward_as_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => crossing_cut_count i (p i))

theorem backward_cut_sum (p : State b) :
    (∑ e ∈ Finset.range (b+1), (backward p e).card)=∑ i : Fin b, (i.val-(p i).val) := by
  simp_rw [backward_as_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => crossing_cut_count (p i) i)

theorem footrule_nat (p : State b) :
    (∑ i : Fin b, ((p i : ℤ)-(i : ℤ)).natAbs)=
      2*∑ e ∈ Finset.range (b+1), halfLoad p e := by
  have habs (i : Fin b) : ((p i : ℤ)-(i : ℤ)).natAbs=
      ((p i).val-i.val)+(i.val-(p i).val) := by
    have h := Int.natCast_natAbs ((p i : ℤ)-(i : ℤ))
    by_cases hi : i.val ≤ (p i).val
    · rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (p i : ℤ)-(i : ℤ))] at h
      omega
    · rw [abs_of_nonpos (by omega : (p i : ℤ)-(i : ℤ) ≤ 0)] at h
      omega
  simp_rw [habs]
  rw [Finset.sum_add_distrib, ← forward_cut_sum, ← backward_cut_sum]
  simp_rw [← cut_balance]
  change (∑ e ∈ Finset.range (b+1), halfLoad p e)+
      (∑ e ∈ Finset.range (b+1), halfLoad p e)= _
  omega

theorem footrule (p : State b) :
    (∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)=
      2*∑ e ∈ Finset.range (b+1), (halfLoad p e : ℤ) := by
  have h := congrArg (fun k : ℕ => (k : ℤ)) (footrule_nat p)
  simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_natAbs] using h

#print axioms half_load_capacity
#print axioms footrule
end LRX.FiniteCuts
