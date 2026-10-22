import LX.OddAlignedObstruction

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem rank_two_unpaid_head_predecessor_values (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hK : HeadPredecessorTerminal p (height p a))
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : p 0=0 ∨ p 0= -1 := by
  by_cases hp0 : p 0=0
  · exact Or.inl hp0
  apply Or.inr
  obtain ⟨hhead,hg1,hg2⟩ := hK
  have hgp : 0 < (-p 0).val := Fin.pos_iff_ne_zero.mpr (neg_ne_zero.mpr hp0)
  have hv1 : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (show 1<n by omega)]
  have hv := Fin.val_add_eq_ite (-p 0) (1 : Fin n)
  have he : -p 0+1=(1 : Fin n)-p 0 := by ring
  rw [he,hv1] at hv
  have hgn := (-p 0).isLt
  have hg : (-p 0).val ≤ height p a+3 := by split_ifs at hv <;> omega
  have hF := (rank_peak_anchor_bounds p a 2 hmin hR).2 0
  have hf : (-p 0).val+2 ≤ (fixedPositions (permutation p 0)).card := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p 0 (by omega) (by omega)
      (by simp only [zero_sub]; omega)
    have hr := anchor_reserve_nonneg p 0
    simp only [zero_sub] at hprice
    exact hunpaid ⟨w,hw,by omega⟩
  have hneg : -p 0=(1 : Fin n) := Fin.ext (by omega)
  linear_combination -hneg

/-- All remaining odd inputs have one of five possible head values.
This is a uniform local restriction, not a finite-size verification. -/
theorem rank_two_unpaid_head_range (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∃ j : ℤ,-3 ≤ j ∧ j ≤ 1 ∧ p 0=(j : Fin n) := by
  classical
  by_cases hJ : ∃ b,HigherAlignedTerminal p (height p a) b
  · obtain ⟨b,hb⟩ := hJ
    exact rank_two_unpaid_aligned_head_range p a b hn hh hR hb hunpaid
  have hbound := odd_unpaid_second_excess_exception_bound p a hn hh hmin hunpaid
  rw [ite_eq_right hJ] at hbound
  have hnonneg : 0 ≤ secondExcess p a := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hK : HeadPredecessorTerminal p (height p a) := by
    by_contra hnot
    rw [ite_eq_right hnot] at hbound
    omega
  rcases rank_two_unpaid_head_predecessor_values p a hn hh hmin hR hK hunpaid with hp0 | hp0
  · exact ⟨0,by omega,by omega,by simpa using hp0⟩
  · exact ⟨-1,by omega,by omega,by simpa using hp0⟩

theorem rank_two_unpaid_inverse_one_position (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) : (p.symm 1).val ≤ 4 := by
  have hdual : ¬ ∃ w : List Letter,reverseDual p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
    rintro ⟨w,hw,hprice⟩
    exact hunpaid ⟨w.reverse,reverse_dual_sorting_word p w hw,by simpa using hprice⟩
  have hheight := reverse_dual_height p a
  obtain ⟨j,hjlo,hjhi,hj⟩ := rank_two_unpaid_head_range (reverseDual p) (dualPosition p a)
    (by omega) (by omega) (reverse_dual_minimum_height p a hmin)
    (fun t => by rw [reverse_dual_rank_surplus]; exact hR t) hdual
  have he : (1 : Fin n)-p.symm 1=(j : Fin n) := by
    simpa only [reverseDual,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
      LRX.WordReflection.reflection_apply,sub_zero] using hj
  have hpre : p.symm 1=((1-j : ℤ) : Fin n) := by
    rw [Int.cast_sub,Int.cast_one]
    linear_combination -he
  have hv : ((1-j).toNat : ℤ)=1-j := Int.toNat_of_nonneg (by omega)
  have hk : (1-j).toNat ≤ 4 := by omega
  have hval : (p.symm 1).val=(1-j).toNat%n := by
    rw [hpre,← hv,Int.cast_natCast]
    rfl
  rw [hval]
  exact (Nat.mod_le _ _).trans hk

theorem odd_unpaid_finite_head_constraints (hn5 : 5 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    (∃ j : ℤ,-3 ≤ j ∧ j ≤ 1 ∧ p 0=(j : Fin n)) ∧ (p.symm 1).val ≤ 4 := by
  obtain ⟨a,_,hnlarge,_,hh,hmin,_,hR,_,_⟩ := odd_unpaid_rank_two_geometry hn5 p m hn hunpaid
  exact ⟨rank_two_unpaid_head_range p a (by omega) (by omega) hmin hR hunpaid,
    rank_two_unpaid_inverse_one_position p a (by omega) (by omega) hmin hR hunpaid⟩

#print axioms rank_two_unpaid_head_range
#print axioms rank_two_unpaid_inverse_one_position
#print axioms odd_unpaid_finite_head_constraints
end LX.AnchoredPhases
