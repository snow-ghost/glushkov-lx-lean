import LX.OddReflectionNeighborFiber
import LX.RankPeakReserve
import LX.LowForwardPayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- The two exceptions to deleting a crossing are paid at their last
minimum-height representative. Its finishing gap is m+3 and its next-depth
count is at most seven. -/
theorem odd_zero_reserve_exception_large (p : State n) (a r u : Fin n)
    (ha : GlobalMinimum p a) (hz : anchorReserve p a=0)
    (m : ℕ) (hn : n=2*m+1) (hh : height p a+1=m) (hm : 4 ≤ m)
    (hu : permutation p a u=u)
    (hp : ∀ i,(p*Equiv.swap u (u+1)) i=r-i)
    (hcase : (r.val=m ∧ u.val=m+1) ∨ (r.val=m+1 ∧ u.val=1)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  let c : Fin n := ⟨m+2,by omega⟩
  have hcval : c.val=m+2 := rfl
  have huv : (u+1).val=u.val+1 := Fin.val_add_one_of_lt' (by rcases hcase with h | h <;> omega)
  have hv : (((m+1 : ℕ) : Fin n)).val=m+1 := Nat.mod_eq_of_lt (by omega)
  have hdval : (u+((m+1 : ℕ) : Fin n)).val=(if u.val=1 then m+2 else 1) := by
    rw [Fin.val_add,hv]
    rcases hcase with h | h
    · rw [h.2,ite_eq_right (by omega : m+1 ≠ 1)]
      have he : m+1+(m+1)=n+1 := by omega
      rw [he,Nat.add_mod,Nat.mod_self,zero_add,Nat.mod_eq_of_lt (by omega : 1<n)]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [h.2,ite_eq_left rfl,Nat.mod_eq_of_lt (by omega : 1+(m+1)<n)]
      omega
  have hrawu : p u-u=p a-a := by
    change p u+(a-p a)=u at hu
    linear_combination hu
  have hrawc : p c-c=p a-a := by
    rw [← hrawu]
    apply (odd_reflection_neighbor_fiber p r u hp m hn (by omega) c).mpr
    rcases hcase with h | h
    · exact Or.inr (Or.inl (Fin.ext (by omega)))
    · apply Or.inr
      apply Or.inr
      apply Fin.ext
      rw [hdval,ite_eq_left h.2]
  have hch : height p c=height p a := by
    have hperm : permutation p c=permutation p a := by
      apply Equiv.ext
      intro j
      change p j+(c-p c)=p j+(a-p a)
      linear_combination -hrawc
    exact congrArg (fun q : State n => (descendingPositions q).card) hperm
  have hfiber (i : Fin n) (hi : p i-i=p a-a) : 0 < i.val ∧ i.val ≤ c.val := by
    have hf := (odd_reflection_neighbor_fiber p r u hp m hn (by omega) i).mp (hi.trans hrawu.symm)
    rcases hf with rfl | rfl | rfl
    · rcases hcase with h | h <;> omega
    · rcases hcase with h | h <;> omega
    · rw [hdval]
      split_ifs <;> omega
  have hhead : p 0 ≠ p c-c := by
    intro he
    have hf := hfiber 0 (by simpa using he.trans hrawc)
    simp only [Fin.val_zero] at hf
    omega
  have hlast (i : Fin n) (hi : p i-i=p c-c) : i.val ≤ c.val := (hfiber i (hi.trans hrawc)).2
  have hpc : (p c).val=n-1 := by
    rcases hcase with h | h
    · have hcv : c=u+1 := Fin.ext (by omega)
      have hpv : p (u+1)=r-u := by simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left] using hp u
      have hlt : r < u := by change r.val < u.val; omega
      rw [hcv,hpv,Fin.coe_sub_iff_lt.mpr hlt]
      omega
    · have hcu : c ≠ u := by intro he; have := congrArg Fin.val he; omega
      have hcv : c ≠ u+1 := by intro he; have := congrArg Fin.val he; omega
      have hpc' : p c=r-c := by
        simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hcu hcv] using hp c
      have hlt : r < c := by change r.val < c.val; omega
      rw [hpc',Fin.coe_sub_iff_lt.mpr hlt]
      omega
  have hgap : (c-p c).val=m+3 := by
    rw [Fin.coe_sub_iff_lt.mpr (show c < p c from by change c.val < (p c).val; omega)]
    omega
  have hR (t : Fin n) : rankSurplus p a t.val ≤ 2 := by
    have hb := critical_rank_peak_reserve p a t ha 1 (by omega)
    rw [hz] at hb
    norm_num at hb
    by_contra hnot
    have hp : 3 ≤ rankSurplus p a t.val := by omega
    nlinarith only [hb,hp,sq_nonneg (rankSurplus p a t.val-2)]
  have hd := rank_peak_next_depth p a 2 hR c (by omega)
  obtain ⟨w,hw,hprice⟩ := low_forward_depth_paid p c (by omega) (Or.inr (by omega))
    hhead hlast (by omega) (by omega) (by omega)
  exact ⟨w,hw,by omega⟩

#print axioms odd_zero_reserve_exception_large
end LX.AnchoredPhases
